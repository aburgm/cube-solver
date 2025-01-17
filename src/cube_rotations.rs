use crate::Rotation;

/// Finds the 24 members of the 3-cube 90-degree rotation
/// group.
pub fn find_cube_rotations() -> Vec<Rotation> {
    let mut result: Vec<Rotation> = vec![];

    for i in 0..4 {
        for j in 0..4 {
            for k in 0..4 {
                let mut m = Rotation::identity();
                for _ in 0..i {
                    m = m.compose(&Rotation::rot_x());
                }
                for _ in 0..j {
                    m = m.compose(&Rotation::rot_y());
                }
                for _ in 0..k {
                    m = m.compose(&Rotation::rot_z());
                }
                if result.iter().find(|cand| **cand == m).is_none() {
                    result.push(m)
                }
            }
        }
    }

    result
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cube_rotations() {
        let r = find_cube_rotations();
        assert_eq!(r.len(), 24);

        assert!(r.iter().find(|x| **x == Rotation::identity()).is_some());
        assert!(r.iter().find(|x| **x == Rotation::rot_x()).is_some());
        assert!(r.iter().find(|x| **x == Rotation::rot_y()).is_some());
        assert!(r.iter().find(|x| **x == Rotation::rot_z()).is_some());
    }
}
