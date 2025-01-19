use crate::{find_cube_rotations, flood_fill, Cube, Piece, Rotation, Vector};

use std::cmp::{max, min};

/// Information about how a piece was placed
#[derive(Default, Debug)]
pub struct Placement {
    /// Anchor cell index of the piece; this cell is placed
    /// at the location specified by `location`
    pub anchor: usize,

    /// Orientation of the piece
    pub orientation: Rotation,

    /// Location inside the cube where the piece is placed
    pub location: Vector,
}

/// Solver state
#[derive(Default)]
pub struct State {
    /// Current occupancy of the cube
    cube: Cube,

    /// Current position where to place the next piece
    cursor: Vector,

    /// Piece orientation to try next
    orientation_index: usize,

    /// Piece anchor to try next
    anchor: usize,
}

pub struct Solver {
    orientations: Box<[Rotation]>,
}

impl State {
    /// Determine whether this state is already unsolvable
    /// if the function returns true, a solution cannot be found
    /// from this state.
    /// If the funciton returns false, a solution *might* still
    /// be findable, but is not guaranteed. Further exploration
    /// is required.
    pub fn is_unsolvable(&self) -> bool {
        let filled = flood_fill(&self.cube);

        for fill in filled {
            if fill.len() % 5 != 0 {
                return true;
            }

            let mut lower = fill[0].clone();
            let mut upper = fill[0].clone();
            for v in &fill[1..] {
                lower = Vector::new(
                    min(lower.at(0), v.at(0)),
                    min(lower.at(1), v.at(1)),
                    min(lower.at(2), v.at(2)),
                );
                upper = Vector::new(
                    max(upper.at(0), v.at(0)),
                    max(upper.at(1), v.at(1)),
                    max(upper.at(2), v.at(2)),
                );
            }

            let extent = upper.sub(&lower);
            let mut extent_components = [extent.at(0), extent.at(1), extent.at(2)];
            extent_components.sort();

            if extent_components[2] < 3 {
                return true;
            }

            if extent_components[1] < 1 {
                return true;
            }
        }

        false
    }
}

impl Solver {
    const SENTINEL: Vector = Vector::new(Cube::LENGTH, Cube::LENGTH, Cube::LENGTH);

    pub fn new() -> Solver {
        Solver {
            orientations: find_cube_rotations().into(),
        }
    }

    pub fn is_complete(state: &State) -> bool {
        state.cursor == Solver::SENTINEL
    }

    /// Returns how the next piece will try to be placed, in this order:
    /// anchor, rotation, translation
    pub fn next_piece(&self, state: &State) -> (usize, Rotation, Vector) {
        (
            state.anchor,
            self.orientations[state.orientation_index].clone(),
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
                        return Solver::SENTINEL;
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
            .rotate(&self.orientations[state.orientation_index])
            .translate(&state.cursor);

        if let Some(cube) = piece.place(&state.cube) {
            let advanced_cursor = Self::advance_cursor(&cube, &state.cursor);
            Some(State {
                cube: cube,
                cursor: advanced_cursor,
                orientation_index: 0,
                anchor: 0,
            })
        } else {
            None
        }
    }

    /// Return a state with the next piece placed. Return None, if none
    /// if no more pieces can be placed.
    pub fn next_candidate(&self, state: &mut State) -> Option<(State, Placement)> {
        while state.anchor < Piece::num_cells() {
            let anchor = state.anchor;
            let orientation_index = state.orientation_index;
            let new_state = self.try_place(state);

            state.orientation_index += 1;
            if state.orientation_index == self.orientations.len() {
                state.orientation_index = 0;
                state.anchor += 1;
            }

            if let Some(new_state) = new_state {
                return Some((
                    new_state,
                    Placement {
                        anchor: anchor,
                        orientation: self.orientations[orientation_index].clone(),
                        location: state.cursor.clone(),
                    },
                ));
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
            Solver::SENTINEL
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
            Solver::SENTINEL
        );
        assert_eq!(
            Solver::advance_cursor(&cube, &Vector::new(4, 4, 4)),
            Solver::SENTINEL
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
        assert_eq!(placed.orientation_index, 0);
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
            orientation_index: 0,
            anchor: 0,
        };
        let solver = Solver::new();

        let placed = solver.try_place(&state).ok_or("Failed to place")?;
        assert!(placed.cube.is_occupied(&Vector::new(0, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(1, 1, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(2, 0, 1)));
        assert!(placed.cube.is_occupied(&Vector::new(3, 0, 1)));
        assert_eq!(placed.cursor, Solver::SENTINEL);
        assert_eq!(placed.orientation_index, 0);
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
            orientation_index: 0,
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
                orientation_index: 0,
                anchor: 0,
            };

            let placed = solver.try_place(&state).ok_or("Failed to place")?;

            assert!(placed.cube.is_occupied(&Vector::new(0, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(1, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(1, 1, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(2, 0, 1)));
            assert!(placed.cube.is_occupied(&Vector::new(3, 0, 1)));
            assert_eq!(placed.cursor, Vector::new(0, 0, 2));
            assert_eq!(placed.orientation_index, 0);
            assert_eq!(placed.anchor, 0);
        }

        {
            let state = State {
                cube: cube.clone(),
                cursor: Vector::new(0, 1, 0),
                orientation_index: 0,
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
            let (next_state, placement) = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place candidate")?;
            assert!(!state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(state.cursor, Vector::new(0, 0, 0));
            assert_eq!(state.orientation_index, 1);
            assert_eq!(state.anchor, 0);

            assert_eq!(placement.anchor, 0);
            assert_eq!(placement.orientation, solver.orientations[0]);
            assert_eq!(placement.location, Vector::new(0, 0, 0));

            assert!(next_state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(next_state.cursor, Vector::new(0, 0, 1));
            assert_eq!(next_state.orientation_index, 0);
            assert_eq!(next_state.anchor, 0);
        }

        for _ in 0..11 {
            let (next_state, placement) = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place candidate")?;
            assert!(!state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert_eq!(state.cursor, Vector::new(0, 0, 0));
            assert!(state.anchor == 0 || state.anchor == 4 || state.anchor == 5);

            assert!(placement.anchor == 0 || placement.anchor == 4);
            assert_eq!(placement.location, Vector::new(0, 0, 0));

            assert!(next_state.cube.is_occupied(&Vector::new(0, 0, 0)));
            assert!(
                next_state.cursor == Vector::new(0, 0, 4)
                    || next_state.cursor == Vector::new(0, 0, 1)
            );
            assert_eq!(next_state.orientation_index, 0);
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
        for (i, free_cell) in FREE_CELLS.iter().enumerate() {
            let mut state = State {
                cube: cube.clone(),
                cursor: free_cell.clone(),
                orientation_index: 0,
                anchor: 0,
            };

            let (next_state, placement) = solver
                .next_candidate(&mut state)
                .ok_or("Failed to place final candidate")?;
            assert!(Solver::is_complete(&next_state));

            assert_eq!(placement.anchor, i);
            assert_eq!(&placement.location, free_cell);

            assert!(solver.next_candidate(&mut state).is_none());
        }

        Ok(())
    }

    fn make_box_hole_cube(min: &Vector, max: &Vector) -> Cube {
        let mut cube = Cube::default();

        for i in min.at(0)..=max.at(0) {
            for j in min.at(0)..=max.at(0) {
                for k in min.at(0)..=max.at(0) {
                    if i == min.at(0) {
                        cube.occupy(&Vector::new(i - 1, j, k));
                    }
                    if i == max.at(0) {
                        cube.occupy(&Vector::new(i + 1, j, k));
                    }
                    if j == min.at(1) {
                        cube.occupy(&Vector::new(i, j - 1, k));
                    }
                    if j == max.at(1) {
                        cube.occupy(&Vector::new(i, j + 1, k));
                    }
                    if k == min.at(2) {
                        cube.occupy(&Vector::new(i, j, k - 1));
                    }
                    if k == max.at(2) {
                        cube.occupy(&Vector::new(i, j, k + 1));
                    }
                }
            }
        }

        cube
    }

    #[test]
    fn test_is_unsolvable_empty() {
        // The pmpty cube should be solvable
        let cube = Cube::default();
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(!state.is_unsolvable());
    }

    #[test]
    fn test_is_unsolvable_with_one_cell_hole() {
        let cube = make_box_hole_cube(&Vector::new(2, 0, 2), &Vector::new(2, 0, 2));
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(state.is_unsolvable());
    }

    #[test]
    fn test_is_unsolvable_with_five_by_one_hole() {
        let cube = make_box_hole_cube(&Vector::new(1, 0, 3), &Vector::new(1, 4, 3));
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(state.is_unsolvable());
    }

    #[test]
    fn test_is_unsolvable_with_two_by_two_hole() {
        let cube = make_box_hole_cube(&Vector::new(1, 1, 3), &Vector::new(3, 3, 3));
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(state.is_unsolvable());
    }

    #[test]
    fn test_is_unsolvable_with_four_by_two_hole() {
        // Four-by-two is not solvable because the number of cells in the hole
        // is not a multiple of 5
        let cube = make_box_hole_cube(&Vector::new(1, 1, 3), &Vector::new(4, 3, 3));
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(state.is_unsolvable());
    }

    #[test]
    fn test_is_unsolvable_with_five_by_two_hole() {
        // A five-by-two whole is not unsolvable yet
        let cube = make_box_hole_cube(&Vector::new(0, 1, 3), &Vector::new(4, 3, 3));
        let state = State {
            cube: cube,
            ..Default::default()
        };
        assert!(!state.is_unsolvable());
    }
}
