#[derive(Clone, Default)]
struct Cube {
    occupancy: [[[bool; 5]; 5]; 5],
}

#[derive(Clone, PartialEq, Default)]
struct Matrix {
    el: [[i32; 3]; 3]
}

#[derive(Clone, PartialEq, Default, Debug)]
struct Vector {
    el: [i32; 3]
}

impl Vector {
    fn at(&self, i: usize) -> i32 {
        self.el[i]
    }

    fn at_mut(&mut self, i: usize) -> &mut i32 {
        &mut self.el[i]
    }

    fn add(&self, vec: &Vector) -> Vector {
        return Vector{
	    el: [self.el[0] + vec.el[0], self.el[1] + vec.el[1], self.el[2] + vec.el[2]],
	}
    }

    fn sub(&self, vec: &Vector) -> Vector {
        return Vector{
	    el: [self.el[0] - vec.el[0], self.el[1] - vec.el[1], self.el[2] - vec.el[2]],
	}
    }
}

impl Matrix {
    fn identity() -> Matrix {
        Matrix{
	    el: [
	        [1,0,0],
		[0,1,0],
		[0,0,1],
	    ],
	}
    }

    fn rot_x() -> Matrix {
        Matrix{
	    el: [
	        [1,0,0],
		[0,0,1],
		[0,-1,0],
	    ],
	}
    }

    fn rot_y() -> Matrix {
        Matrix{
	    el: [
	        [0,0,-1],
		[0,1,0],
		[1,0,0],
	    ],
	}
    }

    fn rot_z() -> Matrix {
        Matrix{
	    el: [
	        [0,1,0],
		[-1,0,0],
		[0,0,1],
	    ],
	}
    }

    fn mul(&self, other: &Matrix) -> Matrix {
        let mut res = Matrix{el: Default::default()};
        for i in 0..3 {
	    for j in 0..3 {
	        for k in 0..3 {
		    *res.at_mut(i, j) += self.at(i, k) * other.at(k, j);
		}
	    }
	}
	res
    }

    fn rotate(&self, vec: &Vector) -> Vector {
        let mut res = Vector{el: Default::default()};

        for i in 0..3 {
	    for j in 0..3 {
	        *res.at_mut(i) += self.at(i,j) * vec.at(j);
	    }
	}

	res
    }

    fn at(&self, i: usize, j: usize) -> i32 {
        self.el[i][j]
    }

    fn at_mut(&mut self, i: usize, j: usize) -> &mut i32 {
        &mut self.el[i][j]
    }
}

impl Cube {
    fn occupy(&mut self, pos: &Vector) -> bool {
        if self.occupied(pos) {
	    return false;
	}

	self.occupancy[pos.at(0) as usize][pos.at(1) as usize][pos.at(2) as usize] = true;
	true
    }

    fn occupied(&self, pos: &Vector) -> bool {
        for i in 0..3 {
            if pos.at(i) < 0 || pos.at(i) >= 5 {
                return true;
	    }
	}

	if self.occupancy[pos.at(0) as usize][pos.at(1) as usize][pos.at(2) as usize] {
	    return true;
	}

	false
    }
}

/// Finds the 24 members of the 3-cube 90-degree rotation
/// group in matrix form.
fn find_cube_rotations() -> Vec<Matrix> {
    let mut result: Vec<Matrix> = vec![];

    for i in 0..4 {
        for j in 0..4 {
            for k in 0..4 {
	        let mut m = Matrix::identity();
	        for _ in 0..i {
		    m = m.mul(&Matrix::rot_x());
		}
	        for _ in 0..j {
		    m = m.mul(&Matrix::rot_y());
		}
	        for _ in 0..k {
		    m = m.mul(&Matrix::rot_z());
		}
		if result.iter().find(|cand| **cand == m).is_none() {
		    result.push(m)
		}
	    }
	}
    }

    result
}

type Layout = [Vector; 5];

fn rotate_piece(piece: &Layout, orientation: &Matrix, center: &Vector) -> Layout {
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
fn place_piece(cube: &Cube, pos: &Vector, orientation: &Matrix, anchor: usize) -> Option<Cube> {
    const PIECE_TEMPLATE: Layout = [
        Vector{el: [0,0,0]},
        Vector{el: [0,1,0]},
        Vector{el: [1,0,0]},
        Vector{el: [2,0,0]},
        Vector{el: [3,0,0]},
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
    orientations: Box<[Matrix]>,
}

impl Solver {
    fn new() -> Solver {
        Solver{
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

	if !cube.occupied(&result) {
	    return result;
	}
    }
}

fn try_place(&self, state: &State) -> Option<State> {
    if let Some(cube) = place_piece(&state.cube, &state.cursor, &self.orientations[state.orientation], state.anchor) {
        Some(State{
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
	      println!("Found a new candidate, now having {}; first orientation={}", cube_track.len(), cube_track[0].orientation);
	    }
	} else {
	    cube_track.pop();
	    if (cube_track.len() < 10) {
	        println!("Iterated all candidates, now having {}; first orientation={}", cube_track.len(), cube_track[0].orientation);
	    }
	}
    }

    println!("No solution found");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_matrix_indexing() {
        let r90 = Matrix::rot_x();
	assert_eq!(r90.at(0,0), 1);
	assert_eq!(r90.at(0,1), 0);
	assert_eq!(r90.at(0,2), 0);
	assert_eq!(r90.at(1,0), 0);
	assert_eq!(r90.at(1,1), 0);
	assert_eq!(r90.at(1,2), 1);
	assert_eq!(r90.at(2,0), 0);
	assert_eq!(r90.at(2,1), -1);
	assert_eq!(r90.at(2,2), 0);
    }

    #[test]
    fn test_cube_rotations() {
        let r = find_cube_rotations();
	assert_eq!(r.len(), 24);
    }
}
