use crate::Vector;

#[derive(Clone, PartialEq)]
pub struct Rotation {
    el: [[i32; 3]; 3],
}

impl Rotation {
    pub const fn identity() -> Rotation {
        Rotation {
            el: [[1, 0, 0], [0, 1, 0], [0, 0, 1]],
        }
    }

    pub const fn rot_x() -> Rotation {
        Rotation {
            el: [[1, 0, 0], [0, 0, 1], [0, -1, 0]],
        }
    }

    pub const fn rot_y() -> Rotation {
        Rotation {
            el: [[0, 0, -1], [0, 1, 0], [1, 0, 0]],
        }
    }

    pub const fn rot_z() -> Rotation {
        Rotation {
            el: [[0, 1, 0], [-1, 0, 0], [0, 0, 1]],
        }
    }

    pub fn compose(&self, other: &Rotation) -> Rotation {
        let mut res = Rotation {
            el: Default::default(),
        };

        for i in 0..3 {
            for j in 0..3 {
                for k in 0..3 {
                    *res.at_mut(i, j) += self.at(i, k) * other.at(k, j);
                }
            }
        }
        res
    }

    pub fn rotate(&self, vec: &Vector) -> Vector {
        let mut res = Vector::default();

        for i in 0..3 {
            for j in 0..3 {
                *res.at_mut(i) += self.at(i, j) * vec.at(j);
            }
        }

        res
    }

    const fn at(&self, i: usize, j: usize) -> i32 {
        self.el[i][j]
    }

    const fn at_mut(&mut self, i: usize, j: usize) -> &mut i32 {
        &mut self.el[i][j]
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic_rotate() {
        let id = Rotation::identity();
        let x90 = Rotation::rot_x();
        let y90 = Rotation::rot_y();
        let z90 = Rotation::rot_z();

        assert_eq!(id.rotate(&Vector::new(1, 0, 0)), Vector::new(1, 0, 0));
        assert_eq!(id.rotate(&Vector::new(0, 1, 0)), Vector::new(0, 1, 0));
        assert_eq!(id.rotate(&Vector::new(0, 0, 1)), Vector::new(0, 0, 1));
        assert_eq!(x90.rotate(&Vector::new(1, 0, 0)), Vector::new(1, 0, 0));
        assert_eq!(x90.rotate(&Vector::new(0, 1, 0)), Vector::new(0, 0, -1));
        assert_eq!(x90.rotate(&Vector::new(0, 0, 1)), Vector::new(0, 1, 0));
        assert_eq!(y90.rotate(&Vector::new(1, 0, 0)), Vector::new(0, 0, 1));
        assert_eq!(y90.rotate(&Vector::new(0, 1, 0)), Vector::new(0, 1, 0));
        assert_eq!(y90.rotate(&Vector::new(0, 0, 1)), Vector::new(-1, 0, 0));
        assert_eq!(z90.rotate(&Vector::new(1, 0, 0)), Vector::new(0, -1, 0));
        assert_eq!(z90.rotate(&Vector::new(0, 1, 0)), Vector::new(1, 0, 0));
        assert_eq!(z90.rotate(&Vector::new(0, 0, 1)), Vector::new(0, 0, 1));
    }

    #[test]
    fn test_combine() {
        const ROTATIONS: [Rotation; 4] = [
            Rotation::identity(),
            Rotation::rot_x(),
            Rotation::rot_y(),
            Rotation::rot_z(),
        ];
        const VECTORS: [Vector; 3] = [
            Vector::new(1, 0, 0),
            Vector::new(0, 1, 0),
            Vector::new(0, 0, 1),
        ];

        for r1 in &ROTATIONS {
            for r2 in &ROTATIONS {
                for v in &VECTORS {
                    assert_eq!(r1.compose(&r2).rotate(&v), r1.rotate(&r2.rotate(&v)));
                }
            }
        }
    }
}
