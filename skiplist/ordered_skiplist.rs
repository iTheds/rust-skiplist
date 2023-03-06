//! 
//! An always-ordered skiplist.
//! 
//! 自动排序跳表
//! 

use crate::skiplist::{
    level_generator::{GeometricalLevelGenerator, LevelGenerator},
    skipnode::{insertion_fixup, removal_fixup, SkipListAction, SkipNode},
};
use std::{cmp, cmp::Ordering, default, fmt, hash, hash::Hash, iter, mem, ops, ops::Bound, ptr};

pub use crate::skiplist::skipnode::{IntoIter, Iter, IterMut};

// ////////////////////////////////////////////////////////////////////////////
// OrderedSkipList，自动排序跳表
// ////////////////////////////////////////////////////////////////////////////

/// 该跳表提供了一种自动排序的方式，同时保证访问、删除和插入节点的效率与 skiplist 一致。
/// 
/// 通常， OrderedSkipList 使用比较函数 `a.partial_cmp(b).expect("Value cannot be ordered")`.
/// 这可以使列表处理 `Ord` 和 `PartialOrd` 的所有类型；
/// 但如果插入了无法排序的值， 如 Float::nan()`， 则会触发异常。
/// 
/// 有序的跳表必须给定一个排序函数，该函数 `f(a,b)` 为保证效率应当满足以下条件：
/// - 定义统一上 ： `f(a, b)` 返回的是相同类型的值;
/// - 符合交换率 ： 如果有 `f(a, b) == Greater` ，那么必然有 `f(b, a) == Less` 和 `f(a, b) == Equal == f(b, a)`.
/// - 具有传递性 ： 如果 `f(a, b) == Greater` 并且 `f(b, c) == Greater` 那么必然有 `f(a, c) == Greater`.
///
/// 注意：如果不满足以上条件，可能导致计算错误、空值或者其他问题。
pub struct OrderedSkipList<T> {
    // Storage, this is not sorted
    head: Box<SkipNode<T>>,
    len: usize,
    level_generator: GeometricalLevelGenerator,
    compare: Box<dyn Fn(&T, &T) -> Ordering>,
}

// ///////////////////////////////////////////////
// Inherent methods，内部方法
// ///////////////////////////////////////////////

impl<T> OrderedSkipList<T>
where
    T: cmp::PartialOrd,
{
    /// 使用默认比较方法 |&a, &b| a.cmp(b).unwrap()` 进行创建新的 skiplist ， 仍然延续默认 16 等级，二分分布方式；
    /// 无法排序的元素将无法进行插入。
    /// 
    /// 比较函数可以通过方法， sort_by 进行修改 ，该方法的消耗可以不计。
    ///
    /// # Panic
    /// 
    /// 如果是无法进行比较的元素例如 `Float::nan()`， 那么插入时将会呼出异常.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist: OrderedSkipList<i64> = OrderedSkipList::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        let lg = GeometricalLevelGenerator::new(16, 1.0 / 2.0);
        OrderedSkipList {
            head: Box::new(SkipNode::head(lg.total())),
            len: 0,
            level_generator: lg,
            compare: (Box::new(|a: &T, b: &T| {
                a.partial_cmp(b).expect("Element cannot be ordered.")
            })) as Box<dyn Fn(&T, &T) -> Ordering>,
        }
    }

    /// 构建一个可容纳 capacity 量级数据的 skiplist， 其计算级数 `floor(log2(capacity))`，
    /// 确保只有少数节点占据最高级别水平，符合 二分分布。
    ///
    /// 使用默认比较函数 `|&a, &b| a.cmp(b).unwrap()`, 可通过 `sort_by` 进行修改。
    ///
    /// # Panic
    ///
    /// 如果是无法进行比较的元素例如 `Float::nan()`， 那么插入时将会呼出异常.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::with_capacity(100);
    /// skiplist.extend(0..100);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        let levels = cmp::max(1, (capacity as f64).log2().floor() as usize);
        let lg = GeometricalLevelGenerator::new(levels, 1.0 / 2.0);
        OrderedSkipList {
            head: Box::new(SkipNode::head(lg.total())),
            len: 0,
            level_generator: lg,
            compare: (Box::new(|a: &T, b: &T| {
                a.partial_cmp(b).expect("Element cannot be ordered.")
            })) as Box<dyn Fn(&T, &T) -> Ordering>,
        }
    }
}

impl<T> OrderedSkipList<T> {
    /// 建立一个新的 skiplist 使用提供的方法进行排序。默认为 16 级。
    ///
    /// # Safety
    /// 
    /// 有序的跳表必须给定一个排序函数，该函数 `f(a,b)` 为保证效率应当满足以下条件：
    /// - 定义统一上 ： `f(a, b)` 返回的是相同类型的值;
    /// - 符合交换率 ： 如果有 `f(a, b) == Greater` ，那么必然有 `f(b, a) == Less` 和 `f(a, b) == Equal == f(b, a)`.
    /// - 具有传递性 ： 如果 `f(a, b) == Greater` 并且 `f(b, c) == Greater` 那么必然有 `f(a, c) == Greater`.
    /// 
    /// **Failure to satisfy these properties can result in unexpected behavior
    /// at best, and at worst will cause a segfault, null deref, or some other
    /// bad behavior.**
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    /// use std::cmp::Ordering;
    ///
    /// // Store even number before odd ones and sort as usual within same parity group.
    /// let mut skiplist = unsafe { OrderedSkipList::with_comp(
    ///     |a: &u64, b: &u64|
    ///     if a%2 == b%2 {
    ///         a.cmp(b)
    ///     } else if a%2 == 0 {
    ///         Ordering::Less
    ///     } else {
    ///         Ordering::Greater
    ///     })};
    /// ```
    #[inline]
    pub unsafe fn with_comp<F>(f: F) -> Self
    where
        F: 'static + Fn(&T, &T) -> Ordering,
    {
        let lg = GeometricalLevelGenerator::new(16, 1.0 / 2.0);
        OrderedSkipList {
            head: Box::new(SkipNode::head(lg.total())),
            len: 0,
            level_generator: lg,
            compare: Box::new(f),
        }
    }

    /// 改变 skiplist 的排序方法。
    ///
    /// # Panics
    ///
    /// This call will panic if the ordering of the elements will be changed as
    /// a result of this new comparison method.
    ///
    /// As a result, `sort_by` is best to call if the skiplist is empty or has
    /// just a single element and may panic with 2 or more elements.
    ///
    /// # Safety
    ///
    /// 有序的跳表必须给定一个可信的排序函数，该函数 `f(a,b)` 为保证效率应当满足以下条件：
    /// - 定义统一上 ： `f(a, b)` 返回的是相同类型的值;
    /// - 符合交换率 ： 如果有 `f(a, b) == Greater` ，那么必然有 `f(b, a) == Less` 和 `f(a, b) == Equal == f(b, a)`.
    /// - 具有传递性 ： 如果 `f(a, b) == Greater` 并且 `f(b, c) == Greater` 那么必然有 `f(a, c) == Greater`.
    ///
    /// **Failure to satisfy these properties can result in unexpected behavior
    /// at best, and at worst will cause a segfault, null deref, or some other
    /// bad behavior.**
    ///
    /// # Examples
    ///
    /// ```should_fail
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// unsafe { skiplist.sort_by(|a: &i64, b: &i64| b.cmp(a)) } // All good; skiplist empty.
    /// skiplist.insert(0);                                      // Would still be good here.
    /// skiplist.insert(10);
    /// unsafe { skiplist.sort_by(|a: &i64, b: &i64| a.cmp(b)) } // Panics; order would change.
    /// ```
    pub unsafe fn sort_by<F>(&mut self, cmp: F)
    where
        F: 'static + Fn(&T, &T) -> Ordering,
    {
        assert!(
            self.is_sort(&cmp),
            "The new ordering does not respect the ordering in the list!"
        );
        self.compare = Box::new(cmp);
    }

    /// 清除 skiplist ， 移除所有值；
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// skiplist.clear();
    /// assert!(skiplist.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
        *self.head = SkipNode::head(self.level_generator.total());
    }
    
    /// 返回跳表元素数量。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.len(), 10);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// 判断是否为空，如果为空，则返回 'true'。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// assert!(skiplist.is_empty());
    ///
    /// skiplist.insert(1);
    /// assert!(!skiplist.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
    /// 插入元素
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    ///
    /// skiplist.insert(0);
    /// skiplist.insert(5);
    /// assert_eq!(skiplist.len(), 2);
    /// assert!(!skiplist.is_empty());
    /// ```
    pub fn insert(&mut self, value: T) {
        let new_node = Box::new(SkipNode::new(value, self.level_generator.random()));
        let inserter = OrdInserter::new(self.compare.as_ref(), new_node);
        let _ = inserter.act(self.head.as_mut());
        self.len += 1;
    }

    /// 获取最开头元素的引用，如果 skiplist 为空则返回 `None`。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// assert!(skiplist.front().is_none());
    ///
    /// skiplist.insert(1);
    /// skiplist.insert(2);
    /// assert_eq!(skiplist.front(), Some(&1));
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            Some(&self[0])
        }
    }
    
    /// 获取最后一个元素的引用，如果 skiplist 为空则返回 `None`。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// assert!(skiplist.back().is_none());
    ///
    /// skiplist.insert(1);
    /// skiplist.insert(2);
    /// assert_eq!(skiplist.back(), Some(&2));
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        let len = self.len();
        if len > 0 {
            Some(&self[len - 1])
        } else {
            None
        }
    }
    
    /// 获取最后指定位置元素的引用，如果 skiplist 为空或者超出长度则返回 `None`。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// assert!(skiplist.get(0).is_none());
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.get(0), Some(&0));
    /// assert!(skiplist.get(10).is_none());
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        let len = self.len();
        if index < len {
            Some(&self[index])
        } else {
            None
        }
    }

    /// 移除第一个元素并且返回， 如果 skiplist 为空则返回 `None`。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.insert(1);
    /// skiplist.insert(2);
    ///
    /// assert_eq!(skiplist.pop_front(), Some(1));
    /// assert_eq!(skiplist.pop_front(), Some(2));
    /// assert!(skiplist.pop_front().is_none());
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(self.remove_index(0))
        }
    }

    /// 移除最后一个元素并且返回， 如果 skiplist 为空则返回 `None`。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.insert(1);
    /// skiplist.insert(2);
    ///
    /// assert_eq!(skiplist.pop_back(), Some(2));
    /// assert_eq!(skiplist.pop_back(), Some(1));
    /// assert!(skiplist.pop_back().is_none());
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        let len = self.len();
        if len > 0 {
            Some(self.remove_index(len - 1))
        } else {
            None
        }
    }

    /// 如果该列表包含该元素，则返回 true.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// assert!(skiplist.contains(&4));
    /// assert!(!skiplist.contains(&15));
    /// ```
    pub fn contains(&self, value: &T) -> bool {
        let (last_lt, _) = self.head.find_last_lt_with(&self.compare, value);
        last_lt
            .next_ref()
            .and_then(|node| node.item.as_ref())
            .map_or(false, |node_value| {
                (self.compare)(value, node_value) == Ordering::Equal
            })
    }

    /// Removes and returns an element with the same value or None if there are
    /// no such values in the skiplist.
    ///
    /// If the skiplist contains multiple values with the desired value, the
    /// highest level one will be removed.  This will results in a deterioration
    /// in the skiplist's performance if the skiplist contains *many* duplicated
    /// values which are very frequently inserted and removed. In such
    /// circumstances, the slower `remove_first` method is preferred.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.remove(&4), Some(4)); // Removes the last one
    /// assert!(skiplist.remove(&4).is_none()); // No more '4' left
    /// ```
    pub fn remove(&mut self, value: &T) -> Option<T> {
        let remover = OrdEagerRemover::new(self.compare.as_ref(), value);
        remover.act(self.head.as_mut()).ok().and_then(|node| {
            self.len -= 1;
            node.into_inner()
        })
    }

    /// Removes and returns an element with the same value or None if there are
    /// no such values in the skiplist.
    ///
    /// If the skiplist contains multiple values with the desired value, the
    /// first one in the skiplist will be returned.  If the skiplist contains
    /// *many* duplicated values which are frequently inserted and removed, this
    /// method should be preferred over `remove`.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// for _ in 0..10 {
    ///     skiplist.extend(0..10);
    /// }
    /// assert!(skiplist.remove(&15).is_none());
    /// for _ in 0..9 {
    ///     for i in 0..10 {
    ///         skiplist.remove_first(&i);
    ///     }
    /// }
    /// assert_eq!(skiplist.remove_first(&4), Some(4)); // Removes the last one
    /// assert!(skiplist.remove_first(&4).is_none()); // No more '4' left
    /// ```
    pub fn remove_first(&mut self, value: &T) -> Option<T> {
        let remover = OrdRemover::new(self.compare.as_ref(), value);
        remover.act(self.head.as_mut()).ok().and_then(|node| {
            self.len -= 1;
            node.into_inner()
        })
    }

    /// Removes and returns an element with the given index.
    ///
    /// # Panics
    ///
    /// Panics is the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// assert_eq!(skiplist.remove_index(4), 4);
    /// assert_eq!(skiplist.remove_index(4), 5);
    /// ```
    pub fn remove_index(&mut self, index: usize) -> T {
        let removed_node = self
            .head
            .remove_at(index)
            .unwrap_or_else(|| panic!("Index out of range"));
        self.len -= 1;
        removed_node.into_inner().unwrap()
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&e)` returns false.
    /// This method operates in place.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// skiplist.retain(|&x| x%2 == 0);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.len -= self.head.retain(move |_, x| f(x));
    }

    /// Removes all repeated elements in the skiplist using the skiplist's
    /// comparison function.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..5);
    /// skiplist.insert(3);
    /// skiplist.dedup();
    /// ```
    pub fn dedup(&mut self) {
        let cmp = self.compare.as_ref();
        let removed = self.head.retain(|prev, current| {
            prev.map_or(true, |prev| (cmp)(prev, current) != Ordering::Equal)
        });
        self.len -= removed;
    }

    /// Get an owning iterator over the entries of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.into_iter() {
    ///     println!("Value: {}", i);
    /// }
    /// ```
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(mut self) -> IntoIter<T> {
        let len = self.len();
        unsafe { IntoIter::from_head(&mut self.head, len) }
    }

    /// Creates an iterator over the entries of the skiplist.
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.iter() {
    ///     println!("Value: {}", i);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<T> {
        let len = self.len();
        unsafe { Iter::from_head(&self.head, len) }
    }
    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// skiplist, starting at min, and ending at max. If min is `Unbounded`,
    /// then it will be treated as "negative infinity", and if max is
    /// `Unbounded`, then it will be treated as "positive infinity".  Thus
    /// range(Unbounded, Unbounded) will yield the whole collection.
    /// 在 skiplist 中的一个子元素范围上构造一个双端迭代器，从 min 开始，到 max 结束。
    /// 如果 min 是 '无界的'，那么它将被视为'负无穷大'；如果 max 是'无界'，则它将被称为 '正无穷大'。
    /// 因此，范围 (Unbounded, Unbounded)  将产生整个集合。
    ///
    /// # Examples
    ///
    /// ```
    /// use skiplist::OrderedSkipList;
    /// use std::ops::Bound::{Included, Unbounded};
    ///
    /// let mut skiplist = OrderedSkipList::new();
    /// skiplist.extend(0..10);
    /// for i in skiplist.range(Included(&3), Included(&7)) {
    ///     println!("Value: {}", i);
    /// }
    /// assert_eq!(Some(&4), skiplist.range(Included(&4), Unbounded).next());
    /// ```
    pub fn range(&self, min: Bound<&T>, max: Bound<&T>) -> Iter<T> {
        self._range(min, max).unwrap_or(Iter {
            first: None,
            last: None,
            size: 0,
        })
    }

    /// 辅助函数，用于简化错误处理。
    fn _range(&self, min: Bound<&T>, max: Bound<&T>) -> Option<Iter<T>> {
        //语法 ： ？？？
        let (first, first_distance_from_head) = match min {
            Bound::Unbounded => (self.head.next_ref()?, 1usize),
            Bound::Included(min) => {
                let (last_lt, last_lt_from_head) = self.head.find_last_lt_with(&self.compare, min);
                let first_ge = last_lt.next_ref()?;
                (first_ge, last_lt_from_head + 1)
            }
            Bound::Excluded(min) => {
                let (last_le, last_le_from_head) = self.head.find_last_le_with(&self.compare, min);
                let first_gt = last_le.next_ref()?;
                (first_gt, last_le_from_head + 1)
            }
        };
        let (last, last_distance_from_head) = match max {
            Bound::Unbounded => (self.head.last(), self.len()),
            Bound::Included(max) => self.head.find_last_le_with(&self.compare, max),
            Bound::Excluded(max) => self.head.find_last_lt_with(&self.compare, max),
        };
        let size = last_distance_from_head.checked_sub(first_distance_from_head)? + 1;
        Some(Iter {
            first: Some(first),
            last: Some(last),
            size,
        })
    }
}

// ///////////////////////////////////////////////
// List Actions
// ///////////////////////////////////////////////

struct OrdInserter<F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    cmp: F,
    new_node: Box<SkipNode<T>>,
}

impl<F, T> OrdInserter<F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    fn new(cmp: F, new_node: Box<SkipNode<T>>) -> Self {
        Self { cmp, new_node }
    }
}

impl<'a, F, T: 'a> SkipListAction<'a, T> for OrdInserter<F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    type Ok = &'a mut SkipNode<T>;

    type Err = Box<SkipNode<T>>;

    fn fail(self) -> Self::Err {
        self.new_node
    }

    fn seek(
        &mut self,
        node: &'a mut SkipNode<T>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<T>, usize)> {
        let value = self.new_node.item.as_ref().unwrap();
        let (node, distance) = node.advance_while_at_level_mut(level, |_current, next| {
            let next_value = next.item.as_ref().unwrap();
            (self.cmp)(value, next_value) == Ordering::Greater
        });
        Some((node, distance))
    }

    // SAEFTY: The new node may never alias with the old nodes.
    unsafe fn act_on_node(self, node: &'a mut SkipNode<T>) -> Result<Self::Ok, Self::Err> {
        // SAFETY: links will be fixed by the caller.
        Ok(node.insert_next(self.new_node))
    }

    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<T>,
        distance_to_target: usize,
        action_result: &mut Self::Ok,
    ) {
        insertion_fixup(level, level_head, distance_to_target, action_result)
    }
}

struct OrdRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    cmp: F,
    target_value: &'a T,
}

impl<'a, F, T> OrdRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    fn new(cmp: F, target_value: &'a T) -> Self {
        Self { cmp, target_value }
    }
}

impl<'a, F, T: 'a> SkipListAction<'a, T> for OrdRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    type Ok = Box<SkipNode<T>>;

    type Err = ();

    #[allow(clippy::unused_unit)]
    fn fail(self) -> Self::Err {
        ()
    }

    fn seek(
        &mut self,
        node: &'a mut SkipNode<T>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<T>, usize)> {
        let (target_parent, distance) = node.advance_while_at_level_mut(level, |_, next_node| {
            (self.cmp)(self.target_value, next_node.item.as_ref().unwrap()) == Ordering::Greater
        });
        if level == 0 {
            let next_value = target_parent
                .next_ref()
                .and_then(|node| node.item.as_ref())?;
            if (self.cmp)(self.target_value, next_value) != Ordering::Equal {
                return None;
            }
        }
        Some((target_parent, distance))
    }

    // SAFETY: The removed node will never alias with nodes in the list.
    unsafe fn act_on_node(self, node: &'a mut SkipNode<T>) -> Result<Self::Ok, Self::Err> {
        // SAFETY: Links will be fixed by the caller.
        node.take_next().ok_or(())
    }

    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<T>,
        _distance_to_target: usize,
        action_result: &mut Self::Ok,
    ) {
        removal_fixup(level, level_head, action_result)
    }
}

struct OrdEagerRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    target_node: *const SkipNode<T>,
    target_value: &'a T,
    cmp: F,
}

impl<'a, F, T> OrdEagerRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    fn new(cmp: F, target_value: &'a T) -> Self {
        Self {
            target_node: ptr::null(),
            target_value,
            cmp,
        }
    }
}

impl<'a, F, T: 'a> SkipListAction<'a, T> for OrdEagerRemover<'a, F, T>
where
    F: Fn(&T, &T) -> Ordering,
{
    type Ok = Box<SkipNode<T>>;

    type Err = ();

    #[allow(clippy::unused_unit)]
    fn fail(self) -> Self::Err {
        ()
    }

    fn seek(
        &mut self,
        node: &'a mut SkipNode<T>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<T>, usize)> {
        if self.target_node.is_null() {
            let (target_parent, distance) =
                node.advance_while_at_level_mut(level, |_, next_node| {
                    (self.cmp)(self.target_value, next_node.item.as_ref().unwrap())
                        == Ordering::Greater
                });
            if level == 0 {
                if let Some(target_value) =
                    target_parent.next_ref().and_then(|node| node.item.as_ref())
                {
                    if (self.cmp)(self.target_value, target_value) == Ordering::Equal {
                        return Some((target_parent, distance));
                    }
                }
                None
            } else {
                if let Some(target_node) =
                    unsafe { target_parent.links[level].and_then(|p| p.as_ptr().as_ref()) }
                {
                    let target_value = target_node.item.as_ref().unwrap();
                    if (self.cmp)(self.target_value, target_value) == Ordering::Equal {
                        self.target_node = target_node as *const _;
                    }
                }
                Some((target_parent, distance))
            }
        } else {
            let (target_parent, distance) = node
                .advance_while_at_level_mut(level, |_, next_node| {
                    !ptr::eq(next_node, self.target_node)
                });
            Some((target_parent, distance))
        }
    }

    // SAFETY: The removed node will never alias with nodes in the list.
    unsafe fn act_on_node(self, node: &'a mut SkipNode<T>) -> Result<Self::Ok, Self::Err> {
        // SAFETY: Links will be fixed by the caller.
        node.take_next().ok_or(())
    }

    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<T>,
        _distance_to_target: usize,
        action_result: &mut Self::Ok,
    ) {
        removal_fixup(level, level_head, action_result)
    }
}

// ///////////////////////////////////////////////
// Internal methods
// ///////////////////////////////////////////////

impl<T> OrderedSkipList<T> {
    fn is_sort(&self, cmp: impl Fn(&T, &T) -> Ordering) -> bool {
        let mut current_node = self.head.as_ref();
        while let Some(next_node) = current_node.next_ref() {
            if let (Some(current_value), Some(next_value)) =
                (current_node.item.as_ref(), next_node.item.as_ref())
            {
                if (cmp)(current_value, next_value) == Ordering::Greater {
                    return false;
                }
            }
            current_node = next_node;
        }
        true
    }
    /// Checks the integrity of the skiplist.
    #[allow(dead_code)]
    fn check(&self) {
        self.head.check();
        assert!(
            self.is_sort(self.compare.as_ref()),
            "The list isn't properly sorted!"
        );
    }

    /// Gets a pointer to the node with the given index.
    fn get_index(&self, index: usize) -> Option<&SkipNode<T>> {
        if self.len() <= index {
            None
        } else {
            self.head.advance(index + 1)
        }
    }
}

impl<T> OrderedSkipList<T>
where
    T: fmt::Debug,
{
    /// 打印 skiplist 的内部结构(用于调试).
    #[allow(dead_code)]
    fn debug_structure(&self) {
        unsafe {
            let mut node: *const SkipNode<T> = mem::transmute_copy(&self.head);
            let mut rows: Vec<_> = iter::repeat(String::new())
                .take(self.level_generator.total())
                .collect();

            loop {
                let value = if let Some(ref v) = (*node).item {
                    format!("> [{:?}]", v)
                } else {
                    "> []".to_string()
                };

                let max_str_len = format!("{} -{}-", value, (*node).links_len[(*node).level]).len();

                let mut lvl = self.level_generator.total();
                while lvl > 0 {
                    lvl -= 1;

                    let mut value_len = if lvl <= (*node).level {
                        format!("{} -{}-", value, (*node).links_len[lvl])
                    } else {
                        format!("{} -", value)
                    };
                    for _ in 0..(max_str_len - value_len.len()) {
                        value_len.push('-');
                    }

                    let mut dashes = String::new();
                    for _ in 0..value_len.len() {
                        dashes.push('-');
                    }

                    if lvl <= (*node).level {
                        rows[lvl].push_str(value_len.as_ref());
                    } else {
                        rows[lvl].push_str(dashes.as_ref());
                    }
                }

                if let Some(next) = (*node).links[0].and_then(|p| p.as_ptr().as_ref()) {
                    node = next;
                } else {
                    break;
                }
            }

            for row in rows.iter().rev() {
                println!("{}", row);
            }
        }
    }
}

// ///////////////////////////////////////////////
// Trait implementation
// ///////////////////////////////////////////////

unsafe impl<T: Send> Send for OrderedSkipList<T> {}
unsafe impl<T: Sync> Sync for OrderedSkipList<T> {}

impl<T: PartialOrd> default::Default for OrderedSkipList<T> {
    fn default() -> OrderedSkipList<T> {
        OrderedSkipList::new()
    }
}

/// This implementation of PartialEq only checks that the *values* are equal; it
/// does not check for equivalence of other features (such as the ordering
/// function and the node levels). Furthermore, this uses `T`'s implementation
/// of PartialEq and *does not* use the owning skiplist's comparison function.
impl<A, B> cmp::PartialEq<OrderedSkipList<B>> for OrderedSkipList<A>
where
    A: cmp::PartialEq<B>,
{
    #[inline]
    fn eq(&self, other: &OrderedSkipList<B>) -> bool {
        self.len() == other.len() && self.iter().eq(other)
    }
    #[allow(clippy::partialeq_ne_impl)]
    #[inline]
    fn ne(&self, other: &OrderedSkipList<B>) -> bool {
        self.len != other.len || self.iter().ne(other)
    }
}

impl<T> cmp::Eq for OrderedSkipList<T> where T: cmp::Eq {}

impl<A, B> cmp::PartialOrd<OrderedSkipList<B>> for OrderedSkipList<A>
where
    A: cmp::PartialOrd<B>,
{
    #[inline]
    fn partial_cmp(&self, other: &OrderedSkipList<B>) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T> Ord for OrderedSkipList<T>
where
    T: cmp::Ord,
{
    #[inline]
    fn cmp(&self, other: &OrderedSkipList<T>) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T> Extend<T> for OrderedSkipList<T> {
    #[inline]
    fn extend<I: iter::IntoIterator<Item = T>>(&mut self, iterable: I) {
        let iterator = iterable.into_iter();
        for element in iterator {
            self.insert(element);
        }
    }
}

impl<T> ops::Index<usize> for OrderedSkipList<T> {
    type Output = T;

    fn index(&self, index: usize) -> &T {
        self.get_index(index)
            .and_then(|node| node.item.as_ref())
            .expect("Index out of range")
    }
}

impl<T> fmt::Debug for OrderedSkipList<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        for (i, entry) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", entry)?;
        }
        write!(f, "]")
    }
}

impl<T> fmt::Display for OrderedSkipList<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;

        for (i, entry) in self.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", entry)?;
        }
        write!(f, "]")
    }
}

impl<T> iter::IntoIterator for OrderedSkipList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        self.into_iter()
    }
}
impl<'a, T> iter::IntoIterator for &'a OrderedSkipList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}
impl<'a, T> iter::IntoIterator for &'a mut OrderedSkipList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T> iter::FromIterator<T> for OrderedSkipList<T>
where
    T: PartialOrd,
{
    #[inline]
    fn from_iter<I>(iter: I) -> OrderedSkipList<T>
    where
        I: iter::IntoIterator<Item = T>,
    {
        let mut skiplist = OrderedSkipList::new();
        skiplist.extend(iter);
        skiplist
    }
}

impl<T: Hash> Hash for OrderedSkipList<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        for elt in self {
            elt.hash(state);
        }
    }
}

// ////////////////////////////////////////////////////////////////////////////
// Tests
// ////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
    use super::OrderedSkipList;
    use std::{
        cmp::Ordering,
        ops::Bound::{self, Excluded, Included, Unbounded},
    };

    #[test]
    fn basic_small() {
        let mut sl: OrderedSkipList<i64> = OrderedSkipList::new();
        sl.check();
        assert!(sl.remove(&1).is_none());
        sl.check();
        sl.insert(1);
        sl.check();
        assert_eq!(sl.remove(&1), Some(1));
        sl.check();
        sl.insert(1);
        sl.check();
        sl.insert(2);
        sl.check();
        assert_eq!(sl.remove(&1), Some(1));
        sl.check();
        assert_eq!(sl.remove(&2), Some(2));
        sl.check();
        assert!(sl.remove(&1).is_none());
        sl.check();
    }

    #[test]
    fn basic_large() {
        let size = 10_000;
        let mut sl = OrderedSkipList::with_capacity(size);
        assert!(sl.is_empty());

        for i in 0..size {
            sl.insert(i);
            assert_eq!(sl.len(), i + 1);
        }
        sl.check();

        for i in 0..size {
            assert_eq!(sl.remove(&i), Some(i));
            assert_eq!(sl.len(), size - i - 1);
        }
        sl.check();
    }

    #[test]
    fn iter() {
        let size = 10000;

        let sl: OrderedSkipList<_> = (0..size).collect();

        fn test<T>(size: usize, mut iter: T)
        where
            T: Iterator<Item = usize>,
        {
            for i in 0..size {
                assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
                assert_eq!(iter.next().unwrap(), i);
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert!(iter.next().is_none());
        }
        test(size, sl.iter().copied());
        test(size, sl.into_iter());
    }

    #[test]
    fn iter_rev() {
        let size = 10000;

        let sl: OrderedSkipList<_> = (0..size).collect();

        fn test<T>(size: usize, mut iter: T)
        where
            T: Iterator<Item = usize>,
        {
            for i in 0..size {
                assert_eq!(iter.size_hint(), (size - i, Some(size - i)));
                assert_eq!(iter.next().unwrap(), size - i - 1);
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert!(iter.next().is_none());
        }
        test(size, sl.iter().rev().copied());
        test(size, sl.into_iter().rev());
    }

    #[test]
    fn iter_mixed() {
        let size = 10000;

        let sl: OrderedSkipList<_> = (0..size).collect();

        fn test<T>(size: usize, mut iter: T)
        where
            T: Iterator<Item = usize> + DoubleEndedIterator,
        {
            for i in 0..size / 4 {
                assert_eq!(iter.size_hint(), (size - i * 2, Some(size - i * 2)));
                assert_eq!(iter.next().unwrap(), i);
                assert_eq!(iter.next_back().unwrap(), size - i - 1);
            }
            for i in size / 4..size * 3 / 4 {
                assert_eq!(iter.size_hint(), (size * 3 / 4 - i, Some(size * 3 / 4 - i)));
                assert_eq!(iter.next().unwrap(), i);
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            assert!(iter.next().is_none());
        }
        test(size, sl.iter().copied());
        test(size, sl.into_iter());
    }

    #[test]
    fn with_comp() {
        let mut sl = unsafe {
            OrderedSkipList::with_comp(|a: &u64, b: &u64| {
                if a % 2 == b % 2 {
                    a.cmp(b)
                } else if a % 2 == 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            })
        };

        for i in 0..100 {
            sl.insert(i);
        }
        sl.check();

        let expect = (0..100)
            .filter(|i| i % 2 == 0)
            .chain((0..100).filter(|i| i % 2 == 1));

        for (&v, e) in sl.iter().zip(expect) {
            assert_eq!(v, e);
        }
    }

    #[test]
    fn sort_by() {
        // Change sort_by when empty
        let mut sl = OrderedSkipList::new();
        unsafe {
            sl.sort_by(|a: &u64, b: &u64| {
                if a % 2 == b % 2 {
                    a.cmp(b)
                } else if a % 2 == 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            });
        };

        for i in 0..100 {
            sl.insert(i);
        }
        sl.check();

        let expect = (0..100)
            .filter(|i| i % 2 == 0)
            .chain((0..100).filter(|i| i % 2 == 1));

        for (&v, e) in sl.iter().zip(expect) {
            assert_eq!(v, e);
        }

        // Change sort_by in non-empty (but valid) skiplist
        let mut sl = OrderedSkipList::new();
        sl.insert(0);
        sl.insert(2);
        sl.insert(5);
        sl.insert(7);
        unsafe {
            sl.sort_by(|a: &u64, b: &u64| {
                if a % 2 == b % 2 {
                    a.cmp(b)
                } else if a % 2 == 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            });
        };
        sl.check();
        sl.insert(4);
        sl.insert(6);
        sl.insert(3);

        for (v, e) in sl.iter().zip(&[0, 2, 4, 6, 3, 5, 7]) {
            assert_eq!(v, e);
        }
    }

    #[test]
    #[should_panic]
    fn sort_by_panic() {
        let mut sl = OrderedSkipList::new();
        sl.insert(0);
        sl.insert(1);
        sl.insert(2);
        unsafe {
            sl.sort_by(|a: &u64, b: &u64| {
                if a % 2 == b % 2 {
                    a.cmp(b)
                } else if a % 2 == 0 {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            });
        };
    }

    #[test]
    fn clear() {
        let mut sl: OrderedSkipList<i64> = (0..100).collect();
        assert_eq!(sl.len(), 100);
        sl.clear();
        sl.check();
        assert!(sl.is_empty());
    }

    #[test]
    fn range_small() {
        let size = 5;
        let sl: OrderedSkipList<_> = (0..size).collect();

        let mut j = 0;
        for (&v, i) in sl.range(Included(&2), Unbounded).zip(2..size) {
            assert_eq!(v, i);
            j += 1;
        }
        assert_eq!(j, size - 2);
    }

    #[test]
    fn range_1000() {
        let size = 1000;
        let sl: OrderedSkipList<_> = (0..size).collect();

        fn test(sl: &OrderedSkipList<u32>, min: Bound<&u32>, max: Bound<&u32>) {
            let mut values = sl.range(min, max);
            #[allow(clippy::range_plus_one)]
            let mut expects = match (min, max) {
                (Excluded(&a), Excluded(&b)) => (a + 1)..b,
                (Included(&a), Excluded(&b)) => a..b,
                (Unbounded, Excluded(&b)) => 0..b,
                (Excluded(&a), Included(&b)) => (a + 1)..(b + 1),
                (Included(&a), Included(&b)) => a..(b + 1),
                (Unbounded, Included(&b)) => 0..(b + 1),
                (Excluded(&a), Unbounded) => (a + 1)..1000,
                (Included(&a), Unbounded) => a..1000,
                (Unbounded, Unbounded) => 0..1000,
            };

            assert_eq!(values.size_hint(), expects.size_hint());

            for (&v, e) in values.by_ref().zip(expects.by_ref()) {
                assert_eq!(v, e);
            }
            assert!(values.next().is_none());
            assert!(expects.next().is_none());
        }

        test(&sl, Excluded(&200), Excluded(&800));
        test(&sl, Included(&200), Excluded(&800));
        test(&sl, Unbounded, Excluded(&800));
        test(&sl, Excluded(&200), Included(&800));
        test(&sl, Included(&200), Included(&800));
        test(&sl, Unbounded, Included(&800));
        test(&sl, Excluded(&200), Unbounded);
        test(&sl, Included(&200), Unbounded);
        test(&sl, Unbounded, Unbounded);
    }

    #[test]
    fn range() {
        let size = 200;
        let sl: OrderedSkipList<_> = (0..size).collect();

        for i in 0..size {
            for j in 0..size {
                let mut values = sl.range(Included(&i), Included(&j));
                let mut expects = i..=j;

                assert_eq!(values.size_hint(), expects.size_hint());

                for (&v, e) in values.by_ref().zip(expects.by_ref()) {
                    assert_eq!(v, e);
                }
                assert!(values.next().is_none());
                assert!(expects.next().is_none());
            }
        }
    }

    #[test]
    fn index_pop() {
        let size = 1000;
        let sl: OrderedSkipList<_> = (0..size).collect();
        assert_eq!(sl.front(), Some(&0));
        assert_eq!(sl.back(), Some(&(size - 1)));
        for i in 0..size {
            assert_eq!(sl[i], i);
            assert_eq!(sl.get(i), Some(&i));
        }

        let mut sl: OrderedSkipList<_> = (0..size).collect();
        for i in 0..size {
            assert_eq!(sl.pop_front(), Some(i));
            assert_eq!(sl.len(), size - i - 1);
        }
        assert!(sl.pop_front().is_none());
        assert!(sl.front().is_none());
        assert!(sl.is_empty());

        let mut sl: OrderedSkipList<_> = (0..size).collect();
        for i in 0..size {
            assert_eq!(sl.pop_back(), Some(size - i - 1));
            assert_eq!(sl.len(), size - i - 1);
        }
        assert!(sl.pop_back().is_none());
        assert!(sl.back().is_none());
        assert!(sl.is_empty());
    }

    #[test]
    fn contains() {
        let (min, max) = (25, 75);
        let sl: OrderedSkipList<_> = (min..max).collect();

        for i in 0..100 {
            if i < min || i >= max {
                assert!(!sl.contains(&i));
            } else {
                assert!(sl.contains(&i));
            }
        }
    }

    #[test]
    fn remove() {
        let size = 100;
        let repeats = 5;
        let mut sl = OrderedSkipList::new();

        for _ in 0..repeats {
            sl.extend(0..size);
        }

        for _ in 0..repeats {
            for i in 0..size {
                assert_eq!(sl.remove(&i), Some(i));
            }
        }
        for i in 0..size {
            assert!(sl.remove(&i).is_none());
        }

        for _ in 0..repeats {
            sl.extend(0..size);
        }
        for _ in 0..repeats {
            for i in 0..size {
                assert_eq!(sl.remove_first(&i), Some(i));
            }
        }
        for i in 0..size {
            assert!(sl.remove_first(&i).is_none());
        }
    }

    #[test]
    fn dedup() {
        let size = 1000;
        let repeats = 10;

        let mut sl: OrderedSkipList<usize> = OrderedSkipList::new();
        for _ in 0..repeats {
            sl.extend(0..size);
        }
        {
            let mut iter = sl.iter();
            for i in 0..size {
                for _ in 0..repeats {
                    assert_eq!(iter.next(), Some(&i));
                }
            }
        }
        sl.dedup();
        sl.check();
        let mut iter = sl.iter();
        for i in 0..size {
            assert_eq!(iter.next(), Some(&i));
        }
    }

    #[test]
    fn retain() {
        let repeats = 10;
        let size = 1000;
        let mut sl: OrderedSkipList<usize> = OrderedSkipList::new();
        for _ in 0..repeats {
            sl.extend(0..size);
        }
        {
            let mut iter = sl.iter();
            for i in 0..size {
                for _ in 0..repeats {
                    assert_eq!(iter.next(), Some(&i));
                }
            }
        }
        sl.retain(|&x| x % 5 == 0);
        sl.check();
        assert_eq!(sl.len(), repeats * size / 5);

        {
            let mut iter = sl.iter();
            for i in 0..size / 5 {
                for _ in 0..repeats {
                    assert_eq!(iter.next(), Some(&(i * 5)));
                }
            }
        }
        sl.retain(|&_| false);
        sl.check();
        assert!(sl.is_empty());
    }

    #[test]
    fn remove_index() {
        let size = 100;

        for i in 0..size {
            let mut sl: OrderedSkipList<_> = (0..size).collect();
            assert_eq!(sl.remove_index(i), i);
            assert_eq!(sl.len(), size - 1);
        }

        let mut sl: OrderedSkipList<_> = (0..size).collect();
        for i in 0..size {
            assert_eq!(sl.remove_index(0), i);
            assert_eq!(sl.len(), size - i - 1);
            sl.check();
        }
        assert!(sl.is_empty());
    }

    #[test]
    fn pop() {
        let size = 1000;
        let mut sl: OrderedSkipList<_> = (0..size).collect();
        for i in 0..size / 2 {
            assert_eq!(sl.pop_front(), Some(i));
            assert_eq!(sl.pop_back(), Some(size - i - 1));
            assert_eq!(sl.len(), size - 2 * (i + 1));
            sl.check();
        }
        assert!(sl.is_empty());
    }

    #[test]
    fn debug_display() {
        let sl: OrderedSkipList<_> = (0..10).collect();
        sl.debug_structure();
        println!("{:?}", sl);
        println!("{}", sl);
    }

    #[test]
    #[allow(clippy::eq_op, clippy::many_single_char_names)]
    fn equality() {
        let a: OrderedSkipList<i64> = (0..100).collect();
        let b: OrderedSkipList<i64> = (0..100).collect();
        let c: OrderedSkipList<i64> = (0..10).collect();
        let d: OrderedSkipList<i64> = (100..200).collect();
        let e: OrderedSkipList<i64> = (0..100).chain(0..1).collect();

        assert_eq!(a, a);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, d);
        assert_ne!(a, e);
        assert_eq!(b, b);
        assert_ne!(b, c);
        assert_ne!(b, d);
        assert_ne!(b, e);
        assert_eq!(c, c);
        assert_ne!(c, d);
        assert_ne!(c, e);
        assert_eq!(d, d);
        assert_ne!(d, e);
        assert_eq!(e, e);
    }
}
