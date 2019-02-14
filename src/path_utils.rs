

pub fn common_prefix(index1:u64, index2:u64) -> u32 {
    (index1 ^ index2).leading_zeros()
}

pub fn has_right_sibling_on_level(index:u64, level:usize) -> bool {
   !has_left_sibling_on_level(index, level)
}

pub fn has_left_sibling_on_level(index:u64, level:usize) -> bool {
    (index >> level) & 1 != 0
}

pub fn calc_unshared_path_len(index1:u64, index2:u64) -> u32 {
    64 - common_prefix(index1, index2) - 1
}


pub fn calc_num_unshared_trailing_elems(main:u64, share:u64) -> u32 {
    calc_num_unshared_leading_elems(!main,!share)
}

pub fn calc_num_unshared_leading_elems(main:u64, share:u64) -> u32 {
    let mask_size = calc_unshared_path_len(main,share);
    let mask = (1 << mask_size) - 1;
    let masked = main & mask;
    masked.count_ones()
}