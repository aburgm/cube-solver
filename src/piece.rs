use crate::{Cube, Rotation, Vector};

pub struct Piece {
    rotation: Rotation,
    translation: Vector,
}

impl Piece {
    const LAYOUT: [Vector; 5] = [
        Vector::new(0, 0, 0),
        Vector::new(1, 0, 0),
        Vector::new(1, 1, 0),
        Vector::new(2, 0, 0),
        Vector::new(3, 0, 0),
    ];

    pub fn num_cells() -> usize {
        Piece::LAYOUT.len()
    }

    /// Create a new piece
    pub fn new() -> Piece {
        Piece {
            rotation: Rotation::identity(),
            translation: Vector::default(),
        }
    }

    /// Try to place the piece in the cube, occupying space
    pub fn place(&self, cube: &Cube) -> Option<Cube> {
        let mut result = cube.clone();
        for v in &Piece::LAYOUT {
            let p = self.transform(&v);
            if !result.occupy(&p) {
                return None;
            }
        }

        return Some(result);
    }

    /// Translates the piece such that the cell with the given
    /// anchor index (between 0 and 4 inclusive) is at the origin
    pub fn anchor(&self, anchor: usize) -> Piece {
        let origin = self.transform(&Piece::LAYOUT[anchor]);
        self.translate(&origin.neg())
    }

    /// Rotate the piece with given rotation around the origin
    pub fn rotate(&self, rotation: &Rotation) -> Piece {
        Piece {
            rotation: rotation.compose(&self.rotation),
            translation: rotation.rotate(&self.translation),
        }
    }

    /// Translate the piece in space
    pub fn translate(&self, translation: &Vector) -> Piece {
        Piece {
            rotation: self.rotation.clone(),
            translation: self.translation.add(&translation),
        }
    }

    fn transform(&self, vec: &Vector) -> Vector {
        self.rotation.rotate(&vec).add(&self.translation)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_default_place() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        let placed = piece.place(&cube).ok_or("failed to place")?;
        assert!(placed.is_occupied(&Vector::new(0, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(1, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(1, 1, 0)));
        assert!(placed.is_occupied(&Vector::new(2, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(3, 0, 0)));
        assert!(!placed.is_occupied(&Vector::new(0, 1, 0)));

        Ok(())
    }

    #[test]
    fn test_translate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        // No space
        assert!(piece
            .translate(&Vector::new(2, 1, 0))
            .place(&cube)
            .is_none());
        assert!(piece
            .translate(&Vector::new(-1, 1, 0))
            .place(&cube)
            .is_none());

        let placed = piece
            .translate(&Vector::new(1, 2, 4))
            .place(&cube)
            .ok_or("failed to place")?;
        assert!(placed.is_occupied(&Vector::new(1, 2, 4)));
        assert!(placed.is_occupied(&Vector::new(2, 2, 4)));
        assert!(placed.is_occupied(&Vector::new(2, 3, 4)));
        assert!(placed.is_occupied(&Vector::new(3, 2, 4)));
        assert!(placed.is_occupied(&Vector::new(4, 2, 4)));
        assert!(!placed.is_occupied(&Vector::new(2, 2, 0)));

        Ok(())
    }

    #[test]
    fn test_rotate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        // No space
        assert!(piece.rotate(&Rotation::rot_x()).place(&cube).is_none());
        assert!(piece.rotate(&Rotation::rot_z()).place(&cube).is_none());

        // Rotation of the base piece around the Y axis works
        let placed = piece
            .rotate(&Rotation::rot_y())
            .place(&cube)
            .ok_or("failed to place")?;

        assert!(placed.is_occupied(&Vector::new(0, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(0, 0, 1)));
        assert!(placed.is_occupied(&Vector::new(0, 1, 1)));
        assert!(placed.is_occupied(&Vector::new(0, 0, 2)));
        assert!(placed.is_occupied(&Vector::new(0, 0, 3)));
        assert!(!placed.is_occupied(&Vector::new(0, 1, 0)));

        Ok(())
    }

    #[test]
    fn test_translate_and_rotate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        // No space
        assert!(piece
            .rotate(&Rotation::rot_x())
            .translate(&Vector::new(0, 2, 0))
            .place(&cube)
            .is_none());

        let placed = piece
            .rotate(&Rotation::rot_x())
            .translate(&Vector::new(0, 0, 2))
            .place(&cube)
            .ok_or("failed to place")?;

        assert!(placed.is_occupied(&Vector::new(0, 0, 2)));
        assert!(placed.is_occupied(&Vector::new(1, 0, 1)));
        assert!(placed.is_occupied(&Vector::new(1, 0, 2)));
        assert!(placed.is_occupied(&Vector::new(2, 0, 2)));
        assert!(placed.is_occupied(&Vector::new(3, 0, 2)));
        assert!(!placed.is_occupied(&Vector::new(0, 0, 1)));

        Ok(())
    }

    #[test]
    fn test_anchor_and_translate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        // No space
        assert!(piece.anchor(1).place(&cube).is_none());
        assert!(piece.anchor(2).place(&cube).is_none());
        assert!(piece.anchor(3).place(&cube).is_none());
        assert!(piece.anchor(4).place(&cube).is_none());

        let placed = piece
            .anchor(3)
            .translate(&Vector::new(3, 0, 0))
            .place(&cube)
            .ok_or("failed to place")?;
        assert!(placed.is_occupied(&Vector::new(1, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(2, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(2, 1, 0)));
        assert!(placed.is_occupied(&Vector::new(3, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(4, 0, 0)));
        assert!(!placed.is_occupied(&Vector::new(1, 1, 0)));

        Ok(())
    }

    #[test]
    fn test_anchor_and_rotate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        // No space
        assert!(piece.anchor(1).place(&cube).is_none());
        assert!(piece.anchor(2).place(&cube).is_none());
        assert!(piece.anchor(3).place(&cube).is_none());
        assert!(piece.anchor(4).place(&cube).is_none());

        let placed = piece
            .anchor(4)
            .rotate(&Rotation::rot_y().compose(&Rotation::rot_y()))
            .place(&cube)
            .ok_or("failed to place")?;

        assert!(placed.is_occupied(&Vector::new(0, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(1, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(2, 1, 0)));
        assert!(placed.is_occupied(&Vector::new(2, 0, 0)));
        assert!(placed.is_occupied(&Vector::new(3, 0, 0)));
        assert!(!placed.is_occupied(&Vector::new(3, 1, 0)));

        Ok(())
    }

    #[test]
    fn test_anchor_translate_and_rotate() -> Result<(), String> {
        let cube = Cube::default();
        let piece = Piece::new();

        let placed = piece
            .anchor(2)
            .rotate(&Rotation::rot_y())
            .translate(&Vector::new(0, 2, 2))
            .place(&cube)
            .ok_or("failed to place")?;

        assert!(placed.is_occupied(&Vector::new(0, 1, 1)));
        assert!(placed.is_occupied(&Vector::new(0, 1, 2)));
        assert!(placed.is_occupied(&Vector::new(0, 2, 2)));
        assert!(placed.is_occupied(&Vector::new(0, 1, 3)));
        assert!(placed.is_occupied(&Vector::new(0, 1, 4)));
        assert!(!placed.is_occupied(&Vector::new(0, 2, 1)));

        Ok(())
    }
}
