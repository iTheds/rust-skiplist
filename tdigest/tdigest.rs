pub struct Centorid{
    mean: f64,
    weight: f64,
}

pub struct Point{
    value: f64,
    weight: f64,
}


pub struct TDigest{
    centorids: Vec<Centorid>,
    centorids_num: usize,
    points: Vec<Point>,
    points_num: usize,
    max_size: usize,
    sum: f64,
    count: f64,
    max: f64,
    min: f64,
}

pub struct SMergeArgs{
    t: Vec<TDigest>,
    centorids: Vec<Centorid>,
    
}