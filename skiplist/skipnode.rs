
//! 
//! 跳表单个节点
//! 

use std::cmp::Ordering;
use std::{
    fmt, iter,
    ptr::{self, NonNull},
};

/// 指向SkipNode的协变指针。
/// SkipNode＜V＞应该包含指向其他节点的可变指针，但可变指针在Rust中不是协变的。适当的指针类型为 std:：ptr:：NonNull 。
/// 有关协方差的详细信息，请参见[`std:：ptr:：NonNull`]和Rustonomicon。
type Link<T> = Option<NonNull<SkipNode<T>>>;

// ////////////////////////////////////////////////////////////////////////////
// 跳表节点
// ////////////////////////////////////////////////////////////////////////////
/// SkipNodes构成SkipList。SkipList拥有第一个头部节点（没有值），每个节点通过“next”拥有下一个节点的所有权。
#[derive(Clone, Debug)]
pub struct SkipNode<V> {
    /// 不为 none , 除非其为 头节点
    pub item: Option<V>,
    /// 节点高度上限
    pub level: usize,
    /// 前节点，作为跳表为什么存的是前置节点
    pub prev: Link<V>,
    /// 指向同级下一个节点的链接容器。此 vec 的长度必须为'self.level+1'。links[0]存储指向下一个节点的指针，该节点将被删除。???
    pub links: Vec<Link<V>>,
    ///每个链接对应长度,表示方法
    pub links_len: Vec<usize>,
}
// ///////////////////////////////////////////////
// SkipNode 方法群
// ///////////////////////////////////////////////
impl<V> SkipNode<V> {
    ///创建头节点
    pub fn head(total_levels: usize) -> Self {
        SkipNode {
            item: None,
            level: total_levels - 1,
            prev: None,
            links: iter::repeat(None).take(total_levels).collect(), 
            // 语法， 这里的 repeat 是 创建一个无限重复单个元素的新迭代器
            // 像 repeat() 这样的无限迭代器经常与像 Iterator::take() 这样的适配器一起使用，以使它们成为有限的。// 但是没有任何对其内存分布的说明，感觉十分不可控
            // Iterator::take(n) 表示取出前 n 个元素
            // Iterator::collect() 是将迭代器转换为集合， Vec 
            links_len: iter::repeat(0).take(total_levels).collect(),
        }
    }
    ///创建一个节点
    pub fn new(item: V, level: usize) -> Self {
        SkipNode {
            item: Some(item),
            level,
            prev: None,
            links: iter::repeat(None).take(level + 1).collect(),
            links_len: iter::repeat(0).take(level + 1).collect(),
        }
    }
    ///获取节点值
    pub fn into_inner(mut self) -> Option<V> {
        self.item.take()
    }
    ///判断是否为头节点
    pub fn is_head(&self) -> bool {
        self.prev.is_none()
    }
    
    pub fn next_ref(&self) -> Option<&Self> {
        // SAFETY: 所有链接要么指向某个对象，要么为空。
        // 语法 ： 闭包用法， 传入 p 值， p.as_ref() 为返回值,取出 p 值的实体；但是 传入的参数是如何确定的，暂时存疑？？？
        unsafe { self.links[0].as_ref().map(|p| p.as_ref()) }
    }
    pub fn next_mut(&mut self) -> Option<&mut Self> {
        // SAFETY: 所有链接要么指向某个对象，要么为空。
        unsafe { self.links[0].as_mut().map(|p| p.as_mut()) }
    }
    /// 获取下一个节点并将 next_node.prev 设置为 null
    /// SAFETY: 请确保1级或更高级别的链接不会悬空。
    pub unsafe fn take_tail(&mut self) -> Option<Box<Self>> {
        self.links[0].take().map(|p| { //语法 ： map 匹配的应该是 take() 返回值之后的内容，后面的闭包处理的是其非空的情况 - 猜的 - 但也对的
            let mut next = Box::from_raw(p.as_ptr());
            next.prev = None;
            self.links_len[0] = 0;
            next
        })
    }
    /// 代替下个节点, 返回旧的节点
    /// SAFETY: 确保所有的 linsk 是固定的
    pub unsafe fn replace_tail(&mut self, mut new_next: Box<Self>) -> Option<Box<Self>> {
        let mut old_next = self.take_tail();
        if let Some(old_next) = old_next.as_mut() {
            old_next.prev = None;
        }
        new_next.prev = Some(NonNull::new_unchecked(self as *mut _));
        self.links[0] = Some(NonNull::new_unchecked(Box::into_raw(new_next)));
        self.links_len[0] = 1;
        old_next
    }
    /// 价值平衡策略
    /// 依靠该节点的携带值
    /// 保留所有具有 pred 的节点, 返回移除的所有节点
    /// 使调用节点成为头节点;
    /// 入参数， F 可能是为 方法
    /// pred 为两参数函数:
    ///     "Option<&V>"是当前节点的值（如果当前节点是头部，则为"None"）
    ///     "&V"是下一个节点的值
    ///     return 如果 pred 返回 false ，则丢弃下一个节点
    #[must_use]
    pub fn retain<F>(&mut self, mut pred: F) -> usize
    where
        F: FnMut(Option<&V>, &V) -> bool,
        // 语法 : 采用可变接受方的调用运算符 ,每天都在猜别人的语法，幸好我猜的还准确
        // 可能是多次调用， 然后传递的参数是可变的。 
    {
        assert!(self.is_head());
        let mut removed_count = 0;
        let mut current_node = self as *mut Self;
        //"level_heads"记录链接列表的每个头节点。
        //head 是给定级别中不在 current_node 之后的最后一个节点。 // 语法 ： repeat 消耗如何 ？？？ 
        let mut level_heads: Vec<_> = iter::repeat(current_node).take(self.level + 1).collect();
        // SAFETY: 一个指针操作块
        unsafe {
            while let Some(mut next_node) = (*current_node).take_tail() {
                // next_node 从列表中删除，按值引用该节点 //pred 应该是一个衡量的方法？？？
                if pred(
                    (*current_node).item.as_ref(), 
                    next_node.item.as_ref().unwrap(),
                ) {
                    // 保持 next_node
                    // 1. 保持更新 等级头节点 level_heads;2. 将 next_node 放回列表
                    for x in &mut level_heads[0..=next_node.level] {
                        *x = next_node.as_mut() as *mut _;
                    }
                    (*current_node).replace_tail(next_node);
                    current_node = (*current_node).next_mut().unwrap();
                } else {
                    // 删除 next_node.
                    removed_count += 1;
                    // 修复 0 级别以上的链接.
                    for (level, head) in level_heads
                        .iter_mut()
                        .map(|&mut node_p| &mut *node_p)
                        .enumerate()
                        .skip(1)
                    {
                        if level <= next_node.level {
                            assert!(ptr::eq(
                                head.links[level].unwrap().as_ptr(),
                                next_node.as_mut()
                            ));
                            head.links_len[level] += next_node.links_len[level];
                            head.links_len[level] -= 1;
                            head.links[level] = next_node.links[level];
                        } else {
                            head.links_len[level] -= 1;
                        }
                    }
                    // 修复 0 级别链接
                    if let Some(new_next) = next_node.take_tail() {
                        (*current_node).replace_tail(new_next);
                    }
                }
            }
        }
        removed_count
    }

    // /////////////////////////////
    // 指针操作,关于整个节点的操作
    // /////////////////////////////
    
    ///当前节点与指定级别的给定节点之间的距离。
    ///如果没有给定节点，则返回当前节点和最后一个可能的节点的距离。
    ///如果在给定级别上无法访问节点，则返回Err(())。
    pub fn distance_at_level(&self, level: usize, target: Option<&Self>) -> Result<usize, ()> {
        let distance = match target { //分处理
            Some(target) => {
                // 语法 : 这个地方应该是， 一个元组，  
                let (dest, distance) =
                    //语法 : 这里的闭包并非是执行，而是返回了一个方法体
                    self.advance_while_at_level(level, |current, _| !ptr::eq(current, target));
                if !ptr::eq(dest, target) {
                    return Err(());
                }
                distance
            }
            None => {
                let (dest, distance) = self.advance_while_at_level(level, |_, _| true);// 默认为 true
                dest.links_len[level] + distance
            }
        };
        Ok(distance)
    }
    ///移动到 max_distance 单位。
    ///如果不可能，则返回 None
    pub fn advance(&self, max_distance: usize) -> Option<&Self> {
        let level = self.level;
        let mut node = self;
        let mut distance_left = max_distance;
        for level in (0..=level).rev() {
            let (new_node, steps) = node.advance_at_level(level, distance_left);
            distance_left -= steps;
            node = new_node;
        }
        if distance_left == 0 {
            Some(node)
        } else {
            None
        }
    }
    ///移动到 max_distance 单位。
    ///如果不可能，则返回 None
    pub fn advance_mut(&mut self, max_distance: usize) -> Option<&mut Self> {
        let level = self.level;
        let mut node = self;
        let mut distance_left = max_distance;
        for level in (0..=level).rev() {
            let (new_node, steps) = node.advance_at_level_mut(level, distance_left);
            distance_left -= steps;
            node = new_node;
        }
        if distance_left == 0 {
            Some(node)
        } else {
            None
        }
    }
    /// 移动到可从此节点访问的最后一个节点。
    pub fn last(&self) -> &Self {
        (0..=self.level).rev().fold(self, |node, level| {
            node.advance_while_at_level(level, |_, _| true).0
        })
    }
    /// 移动到可从此节点访问的最后一个节点。
    pub fn last_mut(&mut self) -> &mut Self {
        (0..=self.level).rev().fold(self, |node, level| {
            node.advance_while_at_level_mut(level, |_, _| true).0
        })
    }
    ///尝试移动给定距离，仅使用指定级别的链接。
    ///如果这是不可能的，那么就尽可能地移动。
    ///返回对新节点和移动距离的引用。
    pub fn advance_at_level(&self, level: usize, mut max_distance: usize) -> (&Self, usize) {
        self.advance_while_at_level(level, move |current_node, _| {
            let travelled = current_node.links_len[level];
            if travelled <= max_distance {
                max_distance -= travelled;
                true
            } else {
                false
            }
        })
    }
    ///尝试移动给定距离，仅使用指定级别的链接。
    ///如果这是不可能的，那么就尽可能地移动。
    ///返回对新节点和移动距离的引用。
    pub fn advance_at_level_mut(
        &mut self,
        level: usize,
        mut max_distance: usize,
    ) -> (&mut Self, usize) {
        self.advance_while_at_level_mut(level, move |current_node, _| {
            let travelled = current_node.links_len[level];
            if travelled <= max_distance {
                max_distance -= travelled;
                true
            } else {
                false
            }
        })
    }
    /// 只要 pred 为真，就保持在指定的级别上移动。
    /// pred 引用当前节点和下一节点。
    pub fn advance_while_at_level(
        &self,
        level: usize,
        mut pred: impl FnMut(&Self, &Self) -> bool,
    ) -> (&Self, usize) {
        let mut current = self;
        let mut travelled = 0;
        loop {
            match current.next_if_at_level(level, &mut pred) {
                Ok((node, steps)) => {
                    current = node;
                    travelled += steps;
                }
                Err(node) => return (node, travelled),
            }
        }
    }
    ///只要 pred 为真，就保持在指定的级别上移动。
    ///pred引用当前节点和下一节点。
    pub fn advance_while_at_level_mut(
        &mut self,
        level: usize,
        mut pred: impl FnMut(&Self, &Self) -> bool,
    ) -> (&mut Self, usize) {
        let mut current = self;
        let mut travelled = 0;
        loop {
            match current.next_if_at_level_mut(level, &mut pred) {
                Ok((node, steps)) => {
                    current = node;
                    travelled += steps;
                }
                Err(node) => return (node, travelled),
            }
        }
    }

    // The following methods return `Err(self)` if they fail.
    // 接下来的模型中，如果返回 Err(self) 即表示失败
    //
    // 在 Rust 中， 返回值的生存周期与 self 变量同等。
    // 因此，如果返回的值是从 self 中假借的， 那么 self 也应该是从其他的分支(？？)处得来的
    //
    // e.g.
    // ```
    // fn some_method(&mut self) -> Option<&mut Self>;
    //
    // fn caller(&mut self) {
    //     match self.some_method(){
    //         Some(x) => return x, // oops now `self` is borrowed until the function returns...假借其他方法中的类，那么在该方法返回时，也将失效
    //         None => return self, // Now you cannot use `self` in other branches..所以，此处不能再返回 self。
    //     }                        // including returning it!包括其他情况的返回
    // }
    // ```
    // While in this example you can restructure the code to fix that,
    // it's much more difficult when loops are involved.
    // The following methods are usually used in loops, so they return `Err(self)`
    // when they fail, to ease the pain.
    // 综上， 虽然在此用例中可以修正来达到继续使用在其他分支的能力.
    // 但实际维护循环时会更加繁琐
    // 所以，在之后频繁使用循环的系列中，如果失败，那么就返回 Err(self)， 以此来减少逻辑上的维护压力 

    /// 如果给定的 predicate 句子成分为 true ， 则移动到 level 的同级别下一个节点
    /// predicate 引用当前节点和下一节点
    pub fn next_if_at_level_mut(
        &mut self,
        level: usize,
        predicate: impl FnOnce(&Self, &Self) -> bool,
    ) -> Result<(&mut Self, usize), &mut Self> {
        // SAFETY: If a link contains Some(p), then p always points to something.
        let next = unsafe { self.links[level].and_then(|p| p.as_ptr().as_mut()) };
        match next {
            Some(next) if predicate(self, next) => Ok((next, self.links_len[level])),
            _ => Err(self),
        }
    }
    /// 如果给定的 predicate 句子成分为 true ， 则移动到 level 的同级别下一个节点
    /// predicate 引用当前节点和下一节点
    pub fn next_if_at_level(
        &self,
        level: usize,
        predicate: impl FnOnce(&Self, &Self) -> bool,
    ) -> Result<(&Self, usize), &Self> {
        // SAFETY: If a link contains Some(p), then p always points to something.
        let next = unsafe { self.links[level].as_ref().map(|p| p.as_ref()) };
        match next {
            Some(next) if predicate(self, next) => Ok((next, self.links_len[level])),
            _ => Err(self),
        }
    }
    /// 在 list head 距离 distance_to_parent 的位置插入一个节点
    ///
    /// Requries that there's nothing before the node and the new node can't be at a higher level.
    ///
    /// Return the reference to the new node if successful.
    /// Give back the input node if not succssful.
    pub fn insert_at(
        &mut self,
        new_node: Box<Self>,
        distance_to_parent: usize,
    ) -> Result<&mut Self, Box<Self>> {
        assert!(self.prev.is_none(), "Only the head may insert nodes!");
        assert!(
            self.level >= new_node.level,
            "You may not insert nodes with level higher than the head!"
        );
        let inserter = IndexInserter::new(distance_to_parent, new_node);
        inserter.act(self)
    }

    /// Move for distance units, and remove the node after it.
    /// 移动指定距离，并且移除下一个节点
    ///
    /// Requries that there's nothing before the node and the new node can't be at a higher level.
    ///
    /// If that node exists, remove that node and retrun it.
    pub fn remove_at(&mut self, distance_to_parent: usize) -> Option<Box<Self>> {
        assert!(self.prev.is_none(), "Only the head may remove nodes!");
        let remover = IndexRemover::new(distance_to_parent);
        remover.act(self).ok()
    }

    /// 校验 list 完整性，调用该方法的必须是头节点 ;
    /// 使用场景如何？？？
    pub fn check(&self) {
        assert!(self.is_head());
        assert!(self.item.is_none());
        let mut current_node = Some(self);
        let mut len = 0;
        // 校验所有节点完整性
        while let Some(node) = current_node {
            // Check the integrity of node.
            assert_eq!(node.level + 1, node.links.len());
            assert_eq!(node.level + 1, node.links_len.len());
            if !node.is_head() {
                assert!(node.item.is_some());
            }
            // Check link at level 0
            if let Some(next_node) = node.next_ref() {
                len += 1;
                assert!(ptr::eq(next_node.prev.unwrap().as_ptr(), node));
            }
            current_node = node.next_ref();
        }

        let len = len; // no mutation

        //校验所有节点的等级策略是否吻合
        for lvl in 1..=self.level {
            let mut length_sum = 0;
            let mut current_node = Some(self);
            while let Some(node) = current_node {
                length_sum += node.links_len[lvl];
                // SAFETY: all links are either None or should points to something.
                let next_node = unsafe { node.links[lvl].as_ref().map(|p| p.as_ref()) };
                assert_eq!(
                    node.links_len[lvl],
                    node.distance_at_level(lvl - 1, next_node).unwrap(),
                    "Node gives different distance at level {} and level {}!",
                    lvl,
                    lvl - 1
                );

                current_node = next_node;
            }

            assert_eq!(length_sum, len);
        }
    }
}


// ///////////////////////////////////////////////
// Trait implementation
// 特性
// ///////////////////////////////////////////////

impl<V> fmt::Display for SkipNode<V>
where
    V: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ref v) = self.item {
            write!(f, "{}", v)
        } else {
            Ok(())
        }
    }
}

// ///////////////////////////////////////////////
// Actions，行为集
// ///////////////////////////////////////////////

/// A SeekListAction seeks a node on the list and do something, e.g. insertion, deletion,
/// replacement, on it, often mutating the links in the process.
/// 
/// 一个 SeekListAction 查找 list 中的节点并且执行动作，如插入/删除/替换，在此过程中，经常会改变链接。
/// 跳表的这些动作经常需要考虑三个方面：
/// 在任意等级中，查找需要修改的目标节点、考虑等级为 0 的情况、在更高的等级中修复跳表
/// 
/// 在任意两个阶段中有一个标准，使用 trait 作为抽象特质
/// 
/// 所以总结，要实现 3 个普适操作：
/// 1. 查找
/// 2. 执行动作
/// 3. 修复链表
/// 
/// 后续的 [IndexInserter] or [IndexRemover] 都是依次而构建的。
///
/// Actions on skiplists usually consist of three phases: for each level, seek the node on which we modify the links,
/// actually modify the link on the 0th level, and fixup the links at upper levels.
///
/// Between the phases there are some bookkeeping, and this trait abstract that away.
///
/// To use this trait, just implement the 3 phases (`seek`, `act_on_node`, `fixup`),
/// and call `act()` on the given list.
///
/// For examples, see one of the types that implements this trait, such as [IndexInserter] or [IndexRemover].
pub trait SkipListAction<'a, T>: Sized {
    /// 返回成功
    type Ok;
    /// 返回失败
    type Err;

    /// 当失败时调用该方法 - 只在 seek() 未找到内容时调用
    fn fail(self) -> Self::Err;

    /// 查找目标节点在给定的等级中
    ///
    /// Return some node and distance travelled.
    /// Return `None` when target node does not exist anywhere in the list.
    /// In this case, the action is considered to have failed, and `Self::fail()` will be called.
    ///
    /// Target node may not exist at a higher level.
    /// You should return some node before the target node in this case.
    /// At level 0 it always finds the target or return `None`.
    fn seek(
        &mut self,
        node: &'a mut SkipNode<T>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<T>, usize)>;

    /// 执行目标行为
    ///
    /// 失败时不调用 fail() ，而是提供更灵活的返回方式
    /// # SAFETY : If `Self::Ok` is a reference, it shall not alias with any node that needs fixup.
    unsafe fn act_on_node(self, node: &'a mut SkipNode<T>) -> Result<Self::Ok, Self::Err>;

    /// Usually SkipListAction breaks links between nodes,  this method should fix that up.
    /// 一般的， SkipListAction 会使链表断开，该方法对其进行修复。
    /// 是一个不应该失败的方法
    /// 
    /// `level_head` is the node whose links may needs to be fixed.
    /// `action_result` is a mutable reference to the return value of act_on_node().
    /// `distance_to_target` is distance from `level_head` to the node that has been acted on.
    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<T>,
        distance_to_target: usize,
        action_result: &mut Self::Ok,
    );

    /// List traversal logic.
    /// 链表遍历逻辑
    /// 
    /// 非特质中需要定义的内容， 适用于所有使用特质的跳表
    /// This handles bookkeeping required for all skiplist mutations.
    ///
    /// It's unlikely one will need to override this.
    /// Override act() instead.
    unsafe fn _traverse(
        mut self,
        node: &'a mut SkipNode<T>,
        level: usize,
    ) -> Result<(Self::Ok, usize), Self::Err> {
        let (level_head, distance_this_level) = match self.seek(node, level) {
            Some(res) => res,
            None => return Err(self.fail()),
        };
        let level_head_p = level_head as *mut SkipNode<T>;
        if level == 0 {
            let mut res = self.act_on_node(level_head)?; //执行继承该特质的动作
            Self::fixup(0, &mut *level_head_p, 0, &mut res);
            Ok((res, distance_this_level))
        } else {
            // 这里递归调用 ，并且 level - 1 , 使得靠近其距离
            let (mut res, distance_after_head) = self._traverse(level_head, level - 1)?;
            let level_head = &mut *level_head_p;
            Self::fixup(level, level_head, distance_after_head, &mut res);
            Ok((res, distance_this_level + distance_after_head))
        }
    }

    /// 执行动作模板
    fn act(self, list_head: &'a mut SkipNode<T>) -> Result<Self::Ok, Self::Err> {
        let (res, _distance) = unsafe { self._traverse(list_head, list_head.level)? };
        Ok(res)
    }
}


// ListActions 辅助方法集
impl<T> SkipNode<T> {
    /// Insert the new node immediatly after this node.
    /// 立即在目标节点后插入节点
    ///
    /// SAFETY: This doesn't fix links at level 1 or higher.
    pub unsafe fn insert_next(&mut self, mut new_node: Box<SkipNode<T>>) -> &mut SkipNode<T> {
        if let Some(tail) = self.take_tail() {
            new_node.replace_tail(tail);
        }
        self.replace_tail(new_node);
        self.next_mut().unwrap()
    }

    /// Take the node immediatly after this node.
    /// 立刻取出当前节点
    ///
    /// SAFETY: This doesn't fix links at level 1 or higher.
    pub unsafe fn take_next(&mut self) -> Option<Box<SkipNode<T>>> {
        let mut ret = self.take_tail()?;
        if let Some(new_tail) = ret.take_tail() {
            self.replace_tail(new_tail);
        }
        Some(ret)
    }
}

/// Helper to seek the node at specific index.
/// 帮助查询特定索引下的节点， 记录的是 self.0 与目标节点的距离。 
/// self.0 is the distance between current node and target.
struct DistanceSeeker(usize);

impl DistanceSeeker {
    /// Find the last node reachable from the given level
    /// whose distance from `node` is no greater than `self.0`.
    /// 在给定级别中，查找最后一个可到达节点，该节点与 node 节点的距离不大于该节点与 self.0 的距离
    /// 
    /// 返回：如果成功，返回该节点，与计算出的距离
    // 语法 : 此处为什么要用一个 'a ？？？
    fn seek<'a, V>(
        &mut self,
        node: &'a mut SkipNode<V>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<V>, usize)> {
        let (node, distance) = node.advance_at_level_mut(level, self.0);
        if level == 0 && distance != self.0 {
            None
        } else {
            self.0 -= distance;
            Some((node, distance))
        }
    }
}

/// Insert a new node at the given index.
/// 插入一个新节点在给定索引范围内
/// See [SkipNode::insert_at] for examples on how to use.
struct IndexInserter<V> {
    index_seek: DistanceSeeker,
    new_node: Box<SkipNode<V>>,
}

impl<V> IndexInserter<V> {
    fn new(distance: usize, new_node: Box<SkipNode<V>>) -> Self {
        IndexInserter {
            index_seek: DistanceSeeker(distance),
            new_node,
        }
    }
}
//重写之前所提到的特质
impl<'a, V: 'a> SkipListAction<'a, V> for IndexInserter<V> {
    type Ok = &'a mut SkipNode<V>;

    type Err = Box<SkipNode<V>>;

    /// Return the would-be-inserted node if fails.
    fn fail(self) -> Self::Err {
        self.new_node
    }

    /// Finds the parent of the new node.
    fn seek(
        &mut self,
        node: &'a mut SkipNode<V>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<V>, usize)> {
        self.index_seek.seek(node, level)
    }

    /// SAFETY: This returns a new node, which should never alias with any old nodes.
    unsafe fn act_on_node(self, node: &'a mut SkipNode<V>) -> Result<Self::Ok, Self::Err> {
        // SAFETY: Links will be fixed by the caller.
        Ok(node.insert_next(self.new_node))
    }

    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<V>,
        distance_to_parent: usize,
        new_node: &mut Self::Ok,
    ) {
        insertion_fixup(level, level_head, distance_to_parent, new_node)
    }
}

/// Remove the node at the given index.
/// 移除节点
/// See [SkipNode::remove_at] for examples on how to use.
struct IndexRemover {
    seeker: DistanceSeeker,
}

impl IndexRemover {
    fn new(distance: usize) -> Self {
        IndexRemover {
            seeker: DistanceSeeker(distance),
        }
    }
}

impl<'a, V> SkipListAction<'a, V> for IndexRemover {
    type Ok = Box<SkipNode<V>>;

    type Err = ();

    /// The only way to fail is when `seek()` does not find an appropriate node,
    /// so we just do nothing.
    #[allow(clippy::unused_unit)]
    fn fail(self) -> Self::Err {
        ()
    }

    fn seek(
        &mut self,
        node: &'a mut SkipNode<V>,
        level: usize,
    ) -> Option<(&'a mut SkipNode<V>, usize)> {
        self.seeker.seek(node, level)
    }

    // SAFETY: Self::Ok is not a reference type
    unsafe fn act_on_node(self, node: &'a mut SkipNode<V>) -> Result<Self::Ok, Self::Err> {
        // SAFETY: links will be fixed by the caller.
        node.take_next().ok_or(())
    }

    fn fixup(
        level: usize,
        level_head: &'a mut SkipNode<V>,
        _distance_to_parent: usize,
        removed_node: &mut Self::Ok,
    ) {
        removal_fixup(level, level_head, removed_node)
    }
}

/// Fixes links at `level` after insertion.
/// 修复指定等级的链表，在执行插入语句之后
/// 
/// 如果可使用，输入新节点在 level_head 之后，并且调整链表长度
/// `distance_to_parent` 表示`level_head` 与 `new_node` 的上级节点距离
/// Put the new_node after level_head if applicable, and adjust link_len.
/// `distance_to_parent` is the distance from `level_head` to the parent of `new_node`.
pub fn insertion_fixup<T>(
    level: usize,
    level_head: &mut SkipNode<T>,
    distance_to_parent: usize,
    new_node: &mut &mut SkipNode<T>,
) {
    if level == 0 {
        // Already handled by insertion.
        return;
    }
    if level <= new_node.level {
        new_node.links[level] = level_head.links[level];
        level_head.links[level] = NonNull::new(*new_node);
        let old_len = level_head.links_len[level];
        new_node.links_len[level] = old_len - distance_to_parent;
        level_head.links_len[level] = distance_to_parent + 1;
    } else {
        level_head.links_len[level] += 1;
    }
}

/// Fix links at the given level after removal.
/// 修复在给定等级下，移除节点后的链表
pub fn removal_fixup<T>(
    level: usize,
    level_head: &mut SkipNode<T>,
    removed_node: &mut Box<SkipNode<T>>,
) {
    if level == 0 {
        return;
    }
    if level <= removed_node.level {
        assert!(ptr::eq(
            level_head.links[level].unwrap().as_ptr(),
            removed_node.as_ref()
        ));
        level_head.links[level] = removed_node.links[level];
        level_head.links_len[level] += removed_node.links_len[level];
    }
    level_head.links_len[level] -= 1;
}

// helpers for ordered types.
// 辅助排序方法集
impl<V> SkipNode<V> {
    /// Find the last node such that f(node.item) returns true.
    /// 查找最后一个节点，满足 f(node.item) 为 true。
    /// 返回节点和移动距离。
    /// Return a reference to the node and distance travelled.
    fn find_ordering_impl<F>(&self, f: F) -> (&Self, usize)
    where
        F: Fn(&V) -> bool,
    {
        (0..=self.level)
            .rev()
            .fold((self, 0), |(node, distance), level| {
                let (node, steps) = node.advance_while_at_level(level, |_, next_node| {
                    let value = next_node.item.as_ref().unwrap();
                    f(value)
                });
                (node, distance + steps)
            })
    }

    /// 查找最后一个节点，满足 f(node.item) 为 true
    /// 返回节点和移动距离
    fn find_ordering_mut_impl<F>(&mut self, f: F) -> (&mut Self, usize)
    where
        F: Fn(&V) -> bool,
    {
        (0..=self.level)
            .rev()
            .fold((self, 0), |(node, distance), level| {
                let (node, steps) = node.advance_while_at_level_mut(level, |_, next_node| {
                    let value = next_node.item.as_ref().unwrap();
                    f(value)
                });
                (node, distance + steps)
            })
    }

    /// Given a list head, a comparison function and a target,
    /// return a reference to the last node whose item compares less than the target,
    /// and the distance to that node.
    /// 给定一个 list head ， 一个比较方法 cmp 和一个目标 target .
    /// 返回对比方法中权值小的节点的引用，以及与该节点的距离。
    pub fn find_last_le_with<F, T: ?Sized>(&self, cmp: F, target: &T) -> (&Self, usize)
    where
        F: Fn(&V, &T) -> Ordering,
    {
        self.find_ordering_impl(|node_value| cmp(node_value, target) != Ordering::Greater)
    }
    /// 给定一个 list head ， 一个比较方法 cmp 和一个目标 target .
    /// 返回对比方法中权值小的节点的可变引用 ，以及与该节点的距离。
    pub fn find_last_le_with_mut<F, T: ?Sized>(&mut self, cmp: F, target: &T) -> (&mut Self, usize)
    where
        F: Fn(&V, &T) -> Ordering,
    {
        self.find_ordering_mut_impl(|node_value| cmp(node_value, target) != Ordering::Greater)
    }

    /// Given a list head, a comparison function and a target,
    /// return a reference to the last node whose item compares less than or equal to the target.
    /// and the distance to that node.
    /// 给定一个 list head ， 一个比较方法 cmp 和一个目标 target .
    /// 返回对比方法中权值小或相等的节点的引用，以及与该节点的距离。
    pub fn find_last_lt_with<F, T: ?Sized>(&self, cmp: F, target: &T) -> (&Self, usize)
    where
        F: Fn(&V, &T) -> Ordering,
    {
        assert!(self.is_head());
        self.find_ordering_impl(|node_value| cmp(node_value, target) == Ordering::Less)
    }
    /// 给定一个 list head ， 一个比较方法 cmp 和一个目标 target .
    /// 返回对比方法中权值小或相等的节点的可变引用，以及与该节点的距离。
    #[allow(dead_code)]
    pub fn find_last_lt_with_mut<F, T: ?Sized>(&mut self, cmp: F, target: &T) -> (&mut Self, usize)
    where
        F: Fn(&V, &T) -> Ordering,
    {
        assert!(self.is_head());
        self.find_ordering_mut_impl(|node_value| cmp(node_value, target) == Ordering::Less)
    }
}

// ///////////////////////////////////////////////
// Helper Traits，辅助特质
// ///////////////////////////////////////////////

// Converting Option<&T> to *_ T becomes more and more annoying...
// 转换 Option<&T> 为 *_ T ，因为该操作的繁琐程度而建立的便利特质；
// 语法 : AsRef and AsMut 是 std::convert 模块下的 trait. 在这里是实现同名的特质，用处也是类型转换
trait AsPtr<T> {
    fn as_ptr(&self) -> *const T;
}

trait AsPtrMut<T> {
    fn as_ptr_mut(&mut self) -> *mut T;
}

impl<T> AsPtr<T> for Option<&T> {
    fn as_ptr(&self) -> *const T {
        self.map_or(ptr::null(), |inner_ref| inner_ref)
    }
}

impl<T> AsPtr<T> for Option<&mut T> {
    fn as_ptr(&self) -> *const T {
        self.as_ref().map_or(ptr::null(), |inner: &&mut T| &**inner)
    }
}

impl<T> AsPtrMut<T> for Option<&mut T> {
    fn as_ptr_mut(&mut self) -> *mut T {
        self.as_mut()
            .map_or(ptr::null_mut(), |inner: &mut &mut T| *inner)
    }
}

// /////////////////////////////////
// Iterators，迭代器
// /////////////////////////////////
// Since Iterators (currently) only pop from front and back,
// they can be shared by some data structures.
// There's no need for a dummy head (that contains no item) in the iterator.
// so the members are named first and last instaed of head/end to avoid confusion.
// 由于当前的迭代器只从前后弹出数据，依此可以共享一些数据结构。
// 不需要假的头节点(无元素实体的容器)在迭代器中，因此第一个元素和最后一个元素将会被分别命名，以避免混淆

/// An iterator for [SkipList](super::SkipList) and [OrderedSkipList](super::OrderedSkipList) .
/// 为 [SkipList](super::SkipList) and [OrderedSkipList](super::OrderedSkipList) 而建立的迭代器
pub struct Iter<'a, T> {
    pub(crate) first: Option<&'a SkipNode<T>>,
    pub(crate) last: Option<&'a SkipNode<T>>,
    pub(crate) size: usize,
}
impl<'a, T> Iter<'a, T> {
    /// SAFETY: There must be `len` nodes after head.
    pub(crate) unsafe fn from_head(head: &'a SkipNode<T>, len: usize) -> Self {
        if len == 0 {
            Iter {
                first: None,
                last: None,
                size: 0,
            }
        } else {
            let first = head.next_ref();
            let last = first.as_ref().map(|n| n.last());
            Iter {
                first,
                last,
                size: len,
            }
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let current_node = self.first?;
        if ptr::eq(current_node, self.last.as_ptr()) {
            self.first = None;
            self.last = None;
        } else {
            self.first = current_node.next_ref();
        }
        self.size -= 1;
        current_node.item.as_ref()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let last_node = self.last?;

        if ptr::eq(self.first.as_ptr(), last_node) {
            self.first = None;
            self.last = None;
        } else {
            // SAFETY: The iterator is not empty yet.
            unsafe {
                self.last = last_node.prev.as_ref().map(|p| p.as_ref());
            }
        }
        self.size -= 1;
        last_node.item.as_ref()
    }
}

/// A mutable iterator for [SkipList](super::SkipList) and [OrderedSkipList](super::OrderedSkipList).
pub struct IterMut<'a, T> {
    pub(crate) first: Option<&'a mut SkipNode<T>>,
    pub(crate) last: Option<NonNull<SkipNode<T>>>,
    pub(crate) size: usize,
}

impl<'a, T> IterMut<'a, T> {
    /// SAFETY: There must be `len` nodes after head.
    pub(crate) unsafe fn from_head(head: &'a mut SkipNode<T>, len: usize) -> Self {
        if len == 0 {
            IterMut {
                first: None,
                last: None,
                size: 0,
            }
        } else {
            let last = NonNull::new(head.last_mut());
            let first = head.next_mut();
            IterMut {
                first,
                last,
                size: len,
            }
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let current_node = self.first.take()?;
        if ptr::eq(current_node, self.last.unwrap().as_ptr()) {
            self.first = None;
            self.last = None;
        } else {
            // calling current_node.next_mut() borrows it, transforming the reference to a pointer
            // unborrows that.
            let p = current_node.next_mut().unwrap() as *mut SkipNode<T>;
            // SAFETY: p.as_mut() is safe because it points to a valid object.
            // There's no aliasing issue since nobody else holds a reference to current_node
            // until this function returns, and the returned reference does not points to a node.
            unsafe {
                self.first = p.as_mut();
            }
        }
        self.size -= 1;
        current_node.item.as_mut()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.last?;
        debug_assert!(self.last.is_some());
        // There can be at most one mutable reference to the first node.
        // We need to take it from self.first before doing anything,
        // including simple comparison.
        let first = self.first.take().unwrap();
        let popped = if ptr::eq(first, self.last.unwrap().as_ptr()) {
            self.last = None;
            first
        } else {
            // SAFETY: self.last isn't null and doesn't alias first
            let new_last = unsafe { self.last.unwrap().as_mut().prev };
            if ptr::eq(first, new_last.unwrap().as_ptr()) {
                self.last = new_last;
                let popped_p = first.next_mut().unwrap() as *mut SkipNode<T>;
                self.first.replace(first);
                unsafe { &mut (*popped_p) }
            } else {
                self.first.replace(first);
                let last = self.last;
                self.last = new_last;
                unsafe { last.unwrap().as_ptr().as_mut().unwrap() }
            }
        };
        self.size -= 1;
        popped.item.as_mut()
    }
}

/// Consuming iterator for [SkipList](super::SkipList), [OrderedSkipList](super::OrderedSkipList) and [SkipMap](super::SkipMap).
pub struct IntoIter<T> {
    pub(crate) first: Option<Box<SkipNode<T>>>,
    pub(crate) last: Option<NonNull<SkipNode<T>>>,
    pub(crate) size: usize,
}

impl<T> IntoIter<T> {
    /// SAFETY: There must be `len` nodes after head.
    pub(crate) unsafe fn from_head(head: &mut SkipNode<T>, len: usize) -> Self {
        if len == 0 {
            IntoIter {
                first: None,
                last: None,
                size: 0,
            }
        } else {
            let last = NonNull::new(head.last_mut());
            let first = head.take_tail();
            IntoIter {
                first,
                last,
                size: len,
            }
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let mut popped_node = self.first.take()?;
        self.size -= 1;
        // SAFETY: no need to fix links at upper levels inside iterators.
        self.first = unsafe { popped_node.take_tail() };
        if self.first.is_none() {
            self.last = None;
        }
        popped_node.into_inner()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.size, Some(self.size))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        #[allow(clippy::question_mark)]
        if self.first.is_none() {
            return None;
        }
        assert!(
            !self.last.is_none(),
            "The IntoIter should be empty but IntoIter.last somehow still contains something"
        );
        let popped_node = if ptr::eq(self.first.as_deref().as_ptr(), self.last.unwrap().as_ptr()) {
            self.last = None;
            self.first.take()?
        } else {
            // SAFETY: we checked that self.last points to somewhere and does not alias to self.first
            let new_last = unsafe { self.last.unwrap().as_mut().prev };
            if ptr::eq(self.first.as_deref().as_ptr(), new_last.unwrap().as_ptr()) {
                // SAFETY: take_tail() is always safe in IntoIter.
                let popped = unsafe {
                    self.first
                        .as_mut()
                        .and_then(|node| node.take_tail())
                        .unwrap()
                };
                self.last = new_last;
                popped
            } else {
                // SAFETY: we checked new_last points to somewhere and do not alias to self.first.
                let popped = unsafe { new_last.unwrap().as_mut().take_tail().unwrap() };
                self.last = new_last;
                popped
            }
        };

        self.size -= 1;
        popped_node.into_inner()
    }
}


// Info : 测试用例应该读的比其他代码更加仔细
#[cfg(test)]
mod test {
    use super::*;

    /// Test test_covariance for SkipNode.
    /// Those functions should compile if our data structures is covariant.
    /// Read Rustonomicon for details.
    /// 
    /// 如果我们的数据结构是协变量， 那么应该编译这些函数；
    /// 该测试用例，似乎是测试参数的输入与返回。
    #[test]
    fn test_covariance() {
        #[allow(dead_code)]
        fn shorten_lifetime<'min, 'max: 'min>(v: SkipNode<&'max ()>) -> SkipNode<&'min ()> {
            v
        }
        #[allow(dead_code)]
        fn shorten_lifetime_into_iter<'min, 'max: 'min>(
            v: IntoIter<&'max ()>,
        ) -> IntoIter<&'min ()> {
            v
        }
        // IterMut is covariant on the value type.
        // This is consistent with Rust reference &'a T.
        #[allow(dead_code)]
        fn shorten_lifetime_iter<'min, 'max: 'min>(
            v: Iter<'max, &'max ()>,
        ) -> Iter<'min, &'min ()> {
            v
        }
        // IterMut is not covariant on the value type.
        // This is consistent with Rust mutable reference type &mut T.
        // TODO: write a test that can't compile
        #[allow(dead_code)]
        fn shorten_lifetime_iter_mut<'min, 'max: 'min>(v: Iter<'max, ()>) -> Iter<'min, ()> {
            v
        }
    }

    /// 测试指定的长度下链表最少需要的等级数量
    fn levels_required(n: usize) -> usize {
        if n == 0 {
            1 // 如果长度是 0 那么 1 个等级即可 -- 我为什么要说废话
        } else {
            // 获取当前系统下 usize 的长度 * 8 ， 也就是 bits 值字节数； <usize> 32 位中是 4 位， 64 位中是 8 位
            let num_bits = std::mem::size_of::<usize>() * 8; 
            // leading_zeros 是调用者的 二进制表示形式 中前导 0 的数量；假设是 64 位系统， n = 1 ， 那么 n 有 8 位， 即是 64 bits, 二进制前导有 63 个 0 。
            // 假设是 64 位系统， 那就是 64 - (n.leading_zeros() as usize) 
            println!("{num_bits} -  {} = {}, {}", n.leading_zeros() as usize, num_bits - n.leading_zeros() as usize, n.leading_zeros());
            num_bits - n.leading_zeros() as usize
            //策略推测 ： 为什么要与 2^n 挂钩 ，等级的数量。 
        }
    }
    #[test]
    fn test_level_required() {
        assert_eq!(levels_required(0), 1);
        assert_eq!(levels_required(1), 1);
        assert_eq!(levels_required(2), 2);
        assert_eq!(levels_required(3), 2);
        assert_eq!(levels_required(10), 4);
        assert_eq!(levels_required(1023), 10);
        assert_eq!(levels_required(1024), 11);
    }

    /// 该函数的作用是， 判断 n 的二进制表示，从最低位开始计数有几位连续的 1 
    /// 该处验证的是 ？？？
    fn level_for_index(mut n: usize) -> usize {
        let mut cnt = 0;
        while n & 0x1 == 1 {
            cnt += 1;
            n /= 2;
        }
        cnt
    }
    #[test]
    fn test_level_index() {
        assert_eq!(level_for_index(0), 0);
        assert_eq!(level_for_index(1), 1);
        assert_eq!(level_for_index(2), 0);
        assert_eq!(level_for_index(3), 2);
        assert_eq!(level_for_index(4), 0);
        assert_eq!(level_for_index(5), 1);
        assert_eq!(level_for_index(6), 0);
        assert_eq!(level_for_index(7), 3);
        assert_eq!(level_for_index(8), 0);
        assert_eq!(level_for_index(9), 1);
        assert_eq!(level_for_index(10), 0);
        assert_eq!(level_for_index(11), 2);
    }

    /// 生成一个长度为 n ，等级分布均匀的跳表 - 长度为 n 的跳表，存储的实际数据节点数 >= n
    fn new_list_for_test(n: usize) -> Box<SkipNode<usize>> {
        let max_level = levels_required(n);//先确定等级数量，no expectation in this library.
        //创建了一个基本的迭代器作为链表的头节点，元素量与等级相同，该头节点存放在 Box 中。
        let mut head = Box::new(SkipNode::<usize>::head(max_level));
        assert_eq!(head.links.len(), max_level);
        //语法 :  Vec<_> 中的 `_` 表示自动推导一个类型，在此处推到出为 Vec<*mut SkipNode<usize>>
        //该处 map 中规定了返回的值是什么， 是一个节点 SkipNode， 该节点中的 link 存储了迭代器的 Vec ， 标志跳表中的一个全等级都有的节点。
        //而 (0..n) 则表示 一个集合， 通过函数 collect() 转换成 Vec ，所以 nodes 表示的是多个拥有全等级的节点的集合
        let mut nodes: Vec<_> = (0..n)
            .map(|n| { // n 作为入参， 生成了 n 个节点， 依照计算？？？等级，生成链表
                // 假设 n 是 10 ，总共有 10 个节点， 等级为 4 ，那么就是有 40 个实际节点， 所以， n 表示的是长度
                let new_node = Box::new(SkipNode::new(n, level_for_index(n)));
                Box::into_raw(new_node) // 返回原始指针，使用 Box 作为容器承载
            })
            .collect();
        //之后的 unsefe 操作，建立在指针上，此时 nodes 类型为 Vec<*mut SkipNode<usize>>
        unsafe {
            //map 中使用闭包函数，进行匹配计算 max ？？？
            let node_max_level = nodes.iter().map(|&node| (*node).level).max();
            if let Some(node_max_level) = node_max_level {
                assert_eq!(node_max_level + 1, max_level); //校验是否与预期一致
            }
            //每个等级都需要进行处理
            for level in 0..max_level {
                let mut last_node = head.as_mut() as *mut SkipNode<usize>;//每个等级都先从头节点开始
                let mut len_left = n;//暂存的计数器
                //当前等级的所有平行的节点进行处理，主要是拼凑和链接
                for &mut node_ptr in nodes
                    // iter_mut 转换为 迭代器的指针 IterMut ， filter() 根据提供的方法筛选出符合条件的元素
                    // 等级需要小于或等于 该节点的 等级
                    .iter_mut()
                    .filter(|&&mut node_ptr| level <= (*node_ptr).level)
                {
                    if level == 0 {//如果是等级 0 ，那么就表示 当前节点 node_ptr 的前序，应该是 head 本身
                        (*node_ptr).prev = NonNull::new(last_node);//拼凑前续指针
                    }
                    (*last_node).links[level] = NonNull::new(node_ptr);//上一个指针的相应等级进行拼接
                    // 注意 : 该处，很关键，长度为 n ， level_left 的起始就是 n ， 等级为 0..max_level
                    // 0 level 即 1 ， 1 level 即 2 ， 2 level 即 4 ， 3 level 即 8， 为二进制中 1 的位数表示 , 即 links_len = 2 ^ level
                    (*last_node).links_len[level] = 1 << level;
                    last_node = node_ptr;// 处理下一个节点
                    // `<<` 的优先级大于 `-=`， 即 len_left -= (1 << level)
                    len_left -= 1 << level;
                }
                //最后一个节点的 links_len 
                //假设有 n = 10, 等级上限为 4 ，最后一个节点 links_len = 10 - (n -1)(2^level) ，那么是有可能为 负数 的
                (*last_node).links_len[level] = len_left;
            }
        }
        head
    }

    /////////////////////////////////////////////////////////
    // Those tests are supposed to be run using Miri to detect UB.
    // The size of those test are limited since Miri doesn't run very fast.
    /////////////////////////////////////////////////////////

    #[test]
    fn miri_test_insert() {
        let mut list = new_list_for_test(50);
        list.insert_at(Box::new(SkipNode::new(100, 0)), 25).unwrap();
        list.insert_at(Box::new(SkipNode::new(101, 1)), 25).unwrap();
        list.insert_at(Box::new(SkipNode::new(102, 2)), 25).unwrap();
        list.insert_at(Box::new(SkipNode::new(103, 3)), 25).unwrap();
        list.insert_at(Box::new(SkipNode::new(104, 4)), 25).unwrap();
    }

    #[test]
    fn miri_test_remove() {
        let mut list = new_list_for_test(50);
        for i in (0..50).rev() {
            list.remove_at(i).unwrap();
        }
    }

    #[test]
    fn miri_test_distance() {
        let list = new_list_for_test(50);
        for i in 0..=list.level {
            let _ = list.distance_at_level(i, None);
        }
    }

    #[test]
    fn miri_test_iter() {
        fn test_iter(size: usize) {
            let list = new_list_for_test(size);
            let first = list.next_ref();
            let last = Some(list.last());
            let mut iter = Iter { first, last, size };
            for _ in 0..(size + 1) / 2 {
                let _ = iter.next();
                let _ = iter.next_back();
            }
            assert!(iter.next().is_none());
        }
        test_iter(9);
        test_iter(10);
    }

    #[test]
    fn miri_test_iter_mut() {
        fn test_iter_mut(size: usize) {
            let mut list = new_list_for_test(size);
            let mut first = list.next_mut();
            let last = first.as_mut().unwrap().last_mut();
            let last = NonNull::new(last);
            let mut iter = IterMut { first, last, size };
            for _ in 0..(size + 1) / 2 {
                let _ = iter.next();
                let _ = iter.next_back();
            }
            assert!(iter.next().is_none());
        }
        test_iter_mut(9);
        test_iter_mut(10);
    }

    #[test]
    fn miri_test_into_iter() {
        fn test_into_iter(size: usize) {
            let mut list = new_list_for_test(size);
            let mut first = unsafe { Some(list.take_tail().unwrap()) };
            let last = first.as_mut().unwrap().last_mut();
            let last = NonNull::new(last);
            let mut iter = IntoIter { first, last, size };
            for _ in 0..(size + 1) / 2 {
                let _ = iter.next();
                let _ = iter.next_back();
            }
            assert!(iter.next().is_none());
        }

        test_into_iter(9);
        test_into_iter(10);
    }

    #[test]
    fn miri_test_retain() {
        let mut list = new_list_for_test(50);
        let _ = list.retain(|_, val| val % 2 == 0);
    }

    #[test]
    fn miri_test_check() {
        let list = new_list_for_test(100);
        list.check();
    }
}
