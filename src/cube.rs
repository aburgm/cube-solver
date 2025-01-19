use crate::Vector;

/// A 5x5x5 cube representation
#[derive(Clone, Default)]
pub struct Cube {
    occupancy: [[[bool; 5]; 5]; 5],
}

impl Cube {
    pub const LENGTH: i32 = 5;

    /// Occupy the given cell in the cube. returns false if the cell
    /// is outside of the cube or is already occupied
    pub fn occupy(&mut self, pos: &Vector) -> bool {
        if self.is_occupied(pos) {
            return false;
        }

        self.occupancy[pos.at(0) as usize][pos.at(1) as usize][pos.at(2) as usize] = true;
        true
    }

    pub fn is_occupied(&self, pos: &Vector) -> bool {
        for i in 0..3 {
            if pos.at(i) < 0 || pos.at(i) >= Cube::LENGTH {
                return true;
            }
        }

        if self.occupancy[pos.at(0) as usize][pos.at(1) as usize][pos.at(2) as usize] {
            return true;
        }

        false
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_occupy() {
        let mut cube = Cube::default();

        for i in 0..Cube::LENGTH {
            for j in 0..Cube::LENGTH {
                for k in 0..Cube::LENGTH {
                    assert!(!cube.is_occupied(&Vector::new(i, j, k)));
                }
            }
        }

        assert!(cube.occupy(&Vector::new(2, 4, 1)));
        assert!(cube.is_occupied(&Vector::new(2, 4, 1)));

        assert!(!cube.occupy(&Vector::new(2, 4, 1)));
        assert!(!cube.is_occupied(&Vector::new(2, 3, 1)));
    }
}
