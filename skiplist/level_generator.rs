//! 
//! SkipList使用内部节点的概率分布级别，其中最低级别（级别0）包含所有节点，每个节点级别`n>0`将包含级别`n-1`上节点的随机子集。
//!
//!最常见的是，使用几何分布，其中节点占据级别 `n` 的机会是 `p` 乘以占据级别 `n-1` 的机会（其中`0<p<1`）。
//! 
//! 这不太可能需要更改，因为默认值应该足够了，但如果需要，可以实现自定义级别生成器。
//! 

use rand::prelude::*;

// ////////////////////////////////////////////////////////////////////////////
// Level Generator，等级生成器特质
// ////////////////////////////////////////////////////////////////////////////

/// 在列表中插入新节点后，该节点将复制分离到高级别；
/// 而复制多少、是否复制将由 `LevelGenerator` 来确定，其具有一定的概率性。
pub trait LevelGenerator {
    /// The total number of levels that are assumed to exist for this level
    /// generator.
    /// 设定此级别生成器存在的级别总数,作为后续概率的约束条件.
    fn total(&self) -> usize;
    /// Generate a random level for a new node in the range `[0, total)`.
    ///
    /// This must never return a level that is `>= self.total()`.
    /// 
    /// 生成一个随机级别在新的节点，其范围是 `[0,total]`; 
    /// 该值的范围处于 `>= self.total()`
    fn random(&mut self) -> usize;
}

/// A level generator which will produce geometrically distributed numbers.
///
/// The probability of generating level `n` is `p` times the probability of
/// generating level `n-1`, with the probability truncated at the maximum number
/// of levels allowed.
/// 生成级别 `n` 的概率是生成级别 `n-1` 的概率的 `p` 倍，概率在允许的最大级别数处截断。
pub struct GeometricalLevelGenerator {
    total: usize,//总共级别
    p: f64, //概率
    // unit_range: distributions::Range<f64>,
    rng: SmallRng, // Fast generator，快速生成
}

impl GeometricalLevelGenerator {
    /// Create a new GeometricalLevelGenerator with `total` number of levels,
    /// and `p` as the probability that a given node is present in the next
    /// level.
    /// 创建一个新的 GeometricalLevelGenerator ，其中 `total` 级别数，`p`表示给定节点出现在下一级别中的概率
    ///
    /// 注意: `p`必须介于0和1之间，否则将死机。同样，`total`必须大于或等于1。
    /// # Panics
    ///
    /// `p` must be between 0 and 1 and will panic otherwise.  Similarly,
    /// `total` must be at greater or equal to 1.
    pub fn new(total: usize, p: f64) -> Self {
        if total == 0 {
            panic!("total must be non-zero.");
        }
        if p <= 0.0 || p >= 1.0 {
            panic!("p must be in (0, 1).");
        }
        GeometricalLevelGenerator {
            total,
            p,
            // unit_range: distributions::Range::new(0.0f64, 1.0),
            rng: SmallRng::from_rng(thread_rng()).unwrap(),//语法 ： thread_rng ，此处似乎是形成了一个随机数生成器
        }
    }
}

// 特质实现
impl LevelGenerator for GeometricalLevelGenerator {
    //该函数应该与跳表的分布方式有关系
    fn random(&mut self) -> usize {
        let mut h = 0;
        let mut x = self.p;
        // f 为 差值
        let f = 1.0 - self.rng.gen::<f64>();
        while x > f && h + 1 < self.total {
            h += 1;
            x *= self.p // h 在单步递增
        }
        h
    }

    fn total(&self) -> usize {
        self.total
    }
}

//具体看 skiplist 实际实现操作
#[cfg(test)]
mod tests {
    use super::GeometricalLevelGenerator;

    #[test]
    #[should_panic]
    fn invalid_total() {
        GeometricalLevelGenerator::new(0, 0.5);
    }

    #[test]
    #[should_panic]
    fn invalid_p_0() {
        GeometricalLevelGenerator::new(1, 0.0);
    }

    #[test]
    #[should_panic]
    fn invalid_p_1() {
        GeometricalLevelGenerator::new(1, 1.0);
    }

    #[test]
    fn new() {
        GeometricalLevelGenerator::new(1, 0.5);
    }
}
