use cube_solver::{find_cube_rotations, Cube, Piece, Rotation, Vector};

#[derive(Default)]
struct State {
    // TODO(armin): add list of pieces placed so far
    cube: Cube,
    cursor: Vector,
    orientation: usize,
    anchor: usize,
}

struct Solver {
    orientations: Box<[Rotation]>,
}

impl Solver {
    fn new() -> Solver {
        Solver {
            orientations: find_cube_rotations().into(),
        }
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

    fn try_place(&self, state: &State) -> Option<State> {
        // TODO(armin): here we want that with its anchor the piece is at the cursor position...
        // but this doesn't do that, does it??
        let piece = Piece::new()
            .anchor(state.anchor)
            .rotate(&self.orientations[state.orientation])
            .translate(&state.cursor);

        if let Some(cube) = piece.place(&state.cube) {
            Some(State {
                cube: cube,
                cursor: Self::advance_cursor(&state.cube, &state.cursor),
                orientation: 0,
                anchor: 0,
            })
        } else {
            None
        }
    }

    /// Create all candidates
    fn next_candidate(&self, state: &mut State) -> Option<State> {
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

fn main() {
    let solver = Solver::new();
    let mut cube_track: Vec<State> = vec![Default::default()];

    while !cube_track.is_empty() {
        let len = cube_track.len();
        if let Some(new_state) = solver.next_candidate(&mut cube_track[len - 1]) {
            if new_state.cursor == Default::default() {
                // we found a winner
                println!("We found a solution!");
                return;
            }
            // If new candidate is final state, we can return
            cube_track.push(new_state);
            if cube_track.len() < 10 {
                println!(
                    "Found a new candidate, now having {}; first orientation={}",
                    cube_track.len(),
                    cube_track[0].orientation
                );
            }
        } else {
            cube_track.pop();
            if cube_track.len() < 10 {
                println!(
                    "Iterated all candidates, now having {}; first orientation={}",
                    cube_track.len(),
                    cube_track[0].orientation
                );
            }
        }
    }

    println!("No solution found");
}
