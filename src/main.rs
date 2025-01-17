use cube_solver::{find_cube_rotations, Cube, Rotation, Vector};

type Layout = [Vector; 5];

fn rotate_piece(piece: &Layout, orientation: &Rotation, center: &Vector) -> Layout {
    let mut result: Layout = Default::default();
    for i in 0..5 {
        result[i] = orientation.rotate(&piece[i].sub(center)).add(center);
    }
    result
}

fn translate_piece(piece: &Layout, translation: &Vector) -> Layout {
    let mut result: Layout = Default::default();
    for i in 0..5 {
        result[i] = piece[i].add(&translation)
    }
    result
}

/// Places a piece at the given position in the given orientation from the given anchor
/// Returns none if piece cannot be placed
fn place_piece(cube: &Cube, pos: &Vector, orientation: &Rotation, anchor: usize) -> Option<Cube> {
    const PIECE_TEMPLATE: Layout = [
        Vector::new(0, 0, 0),
        Vector::new(0, 1, 0),
        Vector::new(1, 0, 0),
        Vector::new(2, 0, 0),
        Vector::new(3, 0, 0),
    ];

    let rotated_piece = rotate_piece(&PIECE_TEMPLATE, orientation, &PIECE_TEMPLATE[anchor]);
    let translated_piece = translate_piece(&rotated_piece, pos);

    let mut result = cube.clone();
    for i in 0..5 {
        if !result.occupy(&translated_piece[i]) {
            return None;
        }
    }

    Some(result)
}

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
        if let Some(cube) = place_piece(
            &state.cube,
            &state.cursor,
            &self.orientations[state.orientation],
            state.anchor,
        ) {
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
