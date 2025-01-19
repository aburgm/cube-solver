use crate::{find_cube_rotations, Cube, Piece, Rotation, Vector};

#[derive(Default)]
pub struct State {
    /// Current occupancy of the cube
    cube: Cube,

    /// Current position where to place the next piece
    cursor: Vector,

    /// Piece orientation to try next
    orientation: usize,

    /// Piece anchor to try next
    anchor: usize,
    // TODO(armin): add last piece info
}

pub struct Solver {
    orientations: Box<[Rotation]>,
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            orientations: find_cube_rotations().into(),
        }
    }

    pub fn is_complete(state: &State) -> bool {
        state.cursor == Vector::default()
    }

    /// Returns how the next piece will try to be placed, in this order:
    /// anchor, rotation, translation
    pub fn next_piece(&self, state: &State) -> (usize, Rotation, Vector) {
        (
            state.anchor,
            self.orientations[state.orientation].clone(),
            state.cursor.clone(),
        )
    }

    fn advance_cursor(cube: &Cube, vec: &Vector) -> Vector {
        let mut result = vec.clone();
        loop {
            *result.at_mut(2) += 1;
            if result.at(2) == 5 {
                *result.at_mut(2) = 0;
                *result.at_mut(1) += 1;
                if result.at(1) == 5 {
                    *result.at_mut(1) = 0;
                    *result.at_mut(0) += 1;
                    if result.at(0) == 5 {
                        return Vector::default(); // not sure?
                    }
                }
            }

            if !cube.is_occupied(&result) {
                return result;
            }
        }
    }

    /// Try to place the next piece in the current state. Return a new
    /// state with the placed piece if it could be placed.
    fn try_place(&self, state: &State) -> Option<State> {
        let piece = Piece::new()
            .anchor(state.anchor)
            .rotate(&self.orientations[state.orientation])
            .translate(&state.cursor);

        if let Some(cube) = piece.place(&state.cube) {
            let advanced_cursor = Self::advance_cursor(&cube, &state.cursor);
            Some(State {
                cube: cube,
                cursor: advanced_cursor,
                orientation: 0,
                anchor: 0,
            })
        } else {
            None
        }
    }

    /// Return a state with the next piece placed. Return None, if none
    /// if no more pieces can be placed.
    pub fn next_candidate(&self, state: &mut State) -> Option<State> {
        while state.anchor < 5 {
            let new_state = self.try_place(state);

            state.orientation += 1;
            if state.orientation == 24 {
                state.orientation = 0;
                state.anchor += 1;
            }

            if new_state.is_some() {
                return new_state;
            }
        }

        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_advance_cursor_with_empty_cube() {
        let cube = Cube::default();
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 0)),
            Vector::new(0, 0, 1)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 1)),
            Vector::new(0, 0, 2)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 4)),
            Vector::new(0, 1, 0)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 1, 0)),
            Vector::new(0, 1, 1)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 1, 3)),
            Vector::new(0, 1, 4)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 1, 4)),
            Vector::new(0, 2, 0)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 4, 3)),
            Vector::new(0, 4, 4)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 4, 4)),
            Vector::new(1, 0, 0)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(1, 3, 2)),
            Vector::new(1, 3, 3)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(1, 3, 4)),
            Vector::new(1, 4, 0)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(4, 4, 4)),
            Vector::default()
        );
    }

    #[test]
    fn test_advance_cursor_with_populated_cube() {
        let mut cube = Cube::default();
        assert!(cube.occupy(&Vector::new(0, 0, 0)));
        assert!(cube.occupy(&Vector::new(0, 1, 0)));
        assert!(cube.occupy(&Vector::new(0, 2, 1)));
        assert!(cube.occupy(&Vector::new(0, 2, 0)));
        assert!(cube.occupy(&Vector::new(0, 3, 0)));
        assert!(cube.occupy(&Vector::new(4, 4, 4)));

        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 0)),
            Vector::new(0, 0, 1)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 1)),
            Vector::new(0, 0, 2)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 0, 4)),
            Vector::new(0, 1, 1)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 1, 4)),
            Vector::new(0, 2, 2)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 2, 2)),
            Vector::new(0, 2, 3)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 2, 4)),
            Vector::new(0, 3, 1)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(0, 3, 4)),
            Vector::new(0, 4, 0)
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(4, 4, 3)),
            Vector::default()
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(4, 4, 4)),
            Vector::default()
        );
    }

    #[test]
    fn test_try_place_initial() -> Result<(), String> {
        let state = State::default();
        let solver = Solver::new();

        let placed = solver.try_place(&state).ok_or("Failed to place")?;

        assert!(placed.cube.is_occupied(&Vector::new(0, 0, 0)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 0, 0)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 1, 0)));
        assert!(placed.cube.is_occupied(&Vector::new(2, 0, 0)));
        assert!(placed.cube.is_occupied(&Vector::new(3, 0, 0)));
        assert!(!placed.cube.is_occupied(&Vector::new(0, 1, 0)));
        assert_eq!(placed.cursor, Vector::new(0, 0, 1));
        assert_eq!(placed.orientation, 0);
        assert_eq!(placed.anchor, 0);

        Ok(())
    }

    #[test]
    fn test_try_place_final() -> Result<(), String> {
        // Make a cube where only one piece is missing
        let mut cube = Cube::default();
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..5 {
                    let v = Vector::new(i, j, k);
                    const FREE_CELLS: [Vector; 5] = [
                        Vector::new(0, 0, 1),
                        Vector::new(1, 0, 1),
                        Vector::new(1, 1, 1),
                        Vector::new(2, 0, 1),
                        Vector::new(3, 0, 1),
                    ];

                    if FREE_CELLS.iter().find(|w| v == **w).is_none() {
                        assert!(cube.occupy(&Vector::new(i, j, k)));
                    }
                }
            }
        }

        let state = State {
            cube: cube,
            cursor: Vector::new(0, 0, 1),
            orientation: 0,
            anchor: 0,
        };
        let solver = Solver::new();

        let placed = solver.try_place(&state).ok_or("Failed to place")?;
        assert!(placed.cube.is_occupied(&Vector::new(0, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 1, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(2, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(3, 0, 1)));
        assert_eq!(placed.cursor, Vector::default());
        assert_eq!(placed.orientation, 0);
        assert_eq!(placed.anchor, 0);

        Ok(())
    }

    #[test]
    fn test_try_place_occupied() {
        let mut cube = Cube::default();
        assert!(cube.occupy(&Vector::new(2, 0, 0)));

        let state = State {
            cube: cube,
            cursor: Vector::default(),
            orientation: 0,
            anchor: 0,
        };
        let solver = Solver::new();

        assert!(solver.try_place(&state).is_none());
    }

    #[test]
    fn test_try_place_intermediate() -> Result<(), String> {
        let mut cube = Cube::default();
        assert!(cube.occupy(&Vector::new(0, 0, 0)));
        assert!(cube.occupy(&Vector::new(1, 0, 0)));
        assert!(cube.occupy(&Vector::new(1, 1, 0)));
        assert!(cube.occupy(&Vector::new(2, 0, 0)));
        assert!(cube.occupy(&Vector::new(3, 0, 0)));

        let solver = Solver::new();

        {
            let state = State {
                cube: cube.clone(),
                cursor: Vector::new(0, 0, 1),
                orientation: 0,
                anchor: 0,
            };

            let placed = solver.try_place(&state).ok_or("Failed to place")?;

            assert!(placed.cube.is_occupied(&Vector::new(0, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(1, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(1, 1, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(2, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(3, 0, 1)));
            assert_eq!(placed.cursor, Vector::new(0, 0, 2));
            assert_eq!(placed.orientation, 0);
            assert_eq!(placed.anchor, 0);
        }

        {
            let state = State {
                cube: cube.clone(),
                cursor: Vector::new(0, 1, 0),
                orientation: 0,
                anchor: 0,
            };

            assert!(solver.try_place(&state).is_none());
        }

        Ok(())
    }

    #[test]
    fn test_next_candidate_initial() -> Result<(), String> {
        let mut state = State::default();
        let solver = Solver::new();

        {
            let next_state = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place candidate")?;
            assert!(!state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(state.cursor, Vector::new(0, 0, 0));
            assert_eq!(state.orientation, 1);
            assert_eq!(state.anchor, 0);

            assert!(next_state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(next_state.cursor, Vector::new(0, 0, 1));
            assert_eq!(next_state.orientation, 0);
            assert_eq!(next_state.anchor, 0);
        }

        for _ in 0..11 {
            let next_state = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place candidate")?;
            assert!(!state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(state.cursor, Vector::new(0, 0, 0));
            assert!(state.anchor == 0 || state.anchor == 4 || state.anchor == 5);

            assert!(next_state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert!(
                next_state.cursor == Vector::new(0, 0, 4)
                    || next_state.cursor == Vector::new(0, 0, 1)
            );
            assert_eq!(next_state.orientation, 0);
            assert_eq!(next_state.anchor, 0);
        }

        assert!(solver.next_candidate(&mut state).is_none());
        Ok(())
    }

    #[test]
    fn test_next_candidate_final() -> Result<(), String> {
        const FREE_CELLS: [Vector; 5] = [
            Vector::new(0, 0, 1),
            Vector::new(1, 0, 1),
            Vector::new(1, 1, 1),
            Vector::new(2, 0, 1),
            Vector::new(3, 0, 1),
        ];
        let solver = Solver::new();

        // Make a cube where only one piece is missing
        let mut cube = Cube::default();
        for i in 0..5 {
            for j in 0..5 {
                for k in 0..5 {
                    let v = Vector::new(i, j, k);
                    if FREE_CELLS.iter().find(|w| v == **w).is_none() {
                        assert!(cube.occupy(&Vector::new(i, j, k)));
                    }
                }
            }
        }

        // For each of the 5 cells of the remaining piece, make a state
        // with one of the free cells at the cursor
        for free_cell in FREE_CELLS {
            let mut state = State {
                cube: cube.clone(),
                cursor: free_cell,
                orientation: 0,
                anchor: 0,
            };

            let next_state = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place final candidate")?;
            assert!(Solver::is_complete(&next_state));

            assert!(solver.next_candidate(&mut state).is_none());
        }

        Ok(())
    }
}
