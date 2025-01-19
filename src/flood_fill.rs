use crate::{Cube, Vector};

type ExplorationState = Cube; //[[[bool; Cube::LENGTH as usize]; Cube::LENGTH as usize]; Cube::LENGTH as usize];

fn flood_fill_from(
    cube: &Cube,
    pos: &Vector,
    exploration_state: &mut ExplorationState,
) -> Vec<Vector> {
    let mut to_be_explored = vec![pos.clone()];
    let mut explored: Vec<Vector> = vec![];

    while let Some(v) = to_be_explored.pop() {
        if !cube.is_occupied(&v) && exploration_state.occupy(&v) {
            to_be_explored.push(Vector::new(v.at(0), v.at(1), v.at(2) - 1));
            to_be_explored.push(Vector::new(v.at(0), v.at(1), v.at(2) + 1));
            to_be_explored.push(Vector::new(v.at(0), v.at(1) - 1, v.at(2)));
            to_be_explored.push(Vector::new(v.at(0), v.at(1) + 1, v.at(2)));
            to_be_explored.push(Vector::new(v.at(0) - 1, v.at(1), v.at(2)));
            to_be_explored.push(Vector::new(v.at(0) + 1, v.at(1), v.at(2)));
            explored.push(v.clone());
        }
    }

    explored
}

/// Run flood fill on the given cube, returning
/// a list of connected sections
pub fn flood_fill(cube: &Cube) -> Vec<Vec<Vector>> {
    // TODO(armin): make it return an iterator, so it's possible to cancel early?
    let mut exploration_state = ExplorationState::default();
    let mut result: Vec<Vec<Vector>> = vec![];

    for i in 0..Cube::LENGTH {
        for j in 0..Cube::LENGTH {
            for k in 0..Cube::LENGTH {
                let v = Vector::new(i, j, k);
                if !cube.is_occupied(&v) && !exploration_state.is_occupied(&v) {
                    result.push(flood_fill_from(cube, &v, &mut exploration_state));
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
    fn test_empty() {
        let cube = Cube::default();

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 1);
        assert_eq!(filled[0].len(), 125);
    }

    #[test]
    fn test_full() {
        let mut cube = Cube::default();

        for i in 0..Cube::LENGTH {
            for j in 0..Cube::LENGTH {
                for k in 0..Cube::LENGTH {
                    assert!(cube.occupy(&Vector::new(i, j, k)));
                }
            }
        }

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 0);
    }

    #[test]
    fn test_one_cell_hole_in_corner() {
        let mut cube = Cube::default();
        assert!(cube.occupy(&Vector::new(4, 0, 3)));
        assert!(cube.occupy(&Vector::new(3, 0, 4)));
        assert!(cube.occupy(&Vector::new(4, 1, 4)));

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 2);
        assert_eq!(filled[0].len(), 121);
        assert_eq!(filled[1].len(), 1);
        assert_eq!(filled[1][0], Vector::new(4, 0, 4));
    }

    #[test]
    fn test_two_cells_hole_in_middle() {
        let mut cube = Cube::default();

        // two-cell-hole
        assert!(cube.occupy(&Vector::new(0, 2, 3)));
        assert!(cube.occupy(&Vector::new(3, 2, 3)));
        assert!(cube.occupy(&Vector::new(1, 1, 3)));
        assert!(cube.occupy(&Vector::new(2, 1, 3)));
        assert!(cube.occupy(&Vector::new(1, 3, 3)));
        assert!(cube.occupy(&Vector::new(2, 3, 3)));
        assert!(cube.occupy(&Vector::new(1, 2, 2)));
        assert!(cube.occupy(&Vector::new(2, 2, 2)));
        assert!(cube.occupy(&Vector::new(1, 2, 4)));
        assert!(cube.occupy(&Vector::new(2, 2, 4)));

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 2);
        assert_eq!(filled[0].len(), 113);
        assert_eq!(filled[1].len(), 2);
        assert_eq!(filled[1][0], Vector::new(1, 2, 3));
        assert_eq!(filled[1][1], Vector::new(2, 2, 3));
    }

    #[test]
    fn test_two_holes() {
        let mut cube = Cube::default();

        // single-cell-hole
        assert!(cube.occupy(&Vector::new(2, 1, 0)));
        assert!(cube.occupy(&Vector::new(2, 1, 2)));
        assert!(cube.occupy(&Vector::new(2, 0, 1)));
        assert!(cube.occupy(&Vector::new(2, 2, 1)));
        assert!(cube.occupy(&Vector::new(1, 1, 1)));
        assert!(cube.occupy(&Vector::new(3, 1, 1)));

        // two-cell-hole
        assert!(cube.occupy(&Vector::new(0, 2, 3)));
        assert!(cube.occupy(&Vector::new(3, 2, 3)));
        assert!(cube.occupy(&Vector::new(1, 1, 3)));
        assert!(cube.occupy(&Vector::new(2, 1, 3)));
        assert!(cube.occupy(&Vector::new(1, 3, 3)));
        assert!(cube.occupy(&Vector::new(2, 3, 3)));
        assert!(cube.occupy(&Vector::new(1, 2, 2)));
        assert!(cube.occupy(&Vector::new(2, 2, 2)));
        assert!(cube.occupy(&Vector::new(1, 2, 4)));
        assert!(cube.occupy(&Vector::new(2, 2, 4)));

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 3);
        assert_eq!(filled[0].len(), 106);
        assert_eq!(filled[1].len(), 2);
        assert_eq!(filled[2].len(), 1);
        assert_eq!(filled[2][0], Vector::new(2, 1, 1));
    }

    #[test]
    fn test_open_hole_in_middle() {
        let mut cube = Cube::default();

        // single-cell-hole
        assert!(cube.occupy(&Vector::new(2, 1, 0)));
        assert!(cube.occupy(&Vector::new(2, 1, 2)));
        assert!(cube.occupy(&Vector::new(2, 0, 1)));
        assert!(cube.occupy(&Vector::new(2, 2, 1)));
        assert!(cube.occupy(&Vector::new(1, 1, 1)));

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 1);
        assert_eq!(filled[0].len(), 120);
    }

    #[test]
    fn test_planar_separation() {
        let mut cube = Cube::default();

        for i in 0..Cube::LENGTH {
            for k in 0..Cube::LENGTH {
                assert!(cube.occupy(&Vector::new(i, 1, k)));
            }
        }

        let filled = flood_fill(&cube);

        assert_eq!(filled.len(), 2);
        assert_eq!(filled[0].len(), 25);
        assert_eq!(filled[1].len(), 75);
    }
}
