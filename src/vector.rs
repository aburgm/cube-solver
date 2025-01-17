#[derive(Clone, PartialEq, Default, Debug)]
pub struct Vector {
    el: [i32; 3],
}

impl Vector {
    pub const fn new(v0: i32, v1: i32, v2: i32) -> Vector {
        Vector { el: [v0, v1, v2] }
    }

    pub fn at(&self, i: usize) -> i32 {
        self.el[i]
    }

    pub fn at_mut(&mut self, i: usize) -> &mut i32 {
        &mut self.el[i]
    }

    pub fn add(&self, vec: &Vector) -> Vector {
        return Vector {
            el: [
                self.el[0] + vec.el[0],
                self.el[1] + vec.el[1],
                self.el[2] + vec.el[2],
            ],
        };
    }

    pub fn sub(&self, vec: &Vector) -> Vector {
        return Vector {
            el: [
                self.el[0] - vec.el[0],
                self.el[1] - vec.el[1],
                self.el[2] - vec.el[2],
            ],
        };
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_vector_default() {
        let v = Vector::default();
        assert_eq!(v.at(0), 0);
        assert_eq!(v.at(1), 0);
        assert_eq!(v.at(2), 0);
    }

    #[test]
    fn test_vector_construct() {
        let v = Vector::new(1, -2, 3);
        assert_eq!(v.at(0), 1);
        assert_eq!(v.at(1), -2);
        assert_eq!(v.at(2), 3);
    }

    #[test]
    fn test_vector_add() {
        let v1 = Vector::new(1, -2, 3);
        let v2 = Vector::new(4, 3, -7);
        let v = v1.add(&v2);

        assert_eq!(v.at(0), 5);
        assert_eq!(v.at(1), 1);
        assert_eq!(v.at(2), -4);
    }

    #[test]
    fn test_vector_sub() {
        let v1 = Vector::new(1, -2, 3);
        let v2 = Vector::new(4, 3, -7);
        let v = v1.sub(&v2);

        assert_eq!(v.at(0), -3);
        assert_eq!(v.at(1), -5);
        assert_eq!(v.at(2), 10);
    }
}
