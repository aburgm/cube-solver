use cube_solver::{Placement, Solver, State};

fn main() {
    let solver = Solver::new();
    let mut cube_track: Vec<(State, Placement)> = vec![Default::default()];

    while !cube_track.is_empty() {
        let len = cube_track.len();
        if let Some((new_state, placement)) = solver.next_candidate(&mut cube_track[len - 1].0) {
            cube_track[len - 1].1 = placement;
            if Solver::is_complete(&new_state) {
                // we found a winner
                println!("We found a solution!");
                return;
            }
            // If new candidate is final state, we can return
            cube_track.push((new_state, Placement::default()));
            if cube_track.len() < 10 {
                println!(
                    "Found a new candidate, now having {}; first placement={:?}",
                    cube_track.len(),
                    cube_track[0].1,
                );
            }
        } else {
            cube_track.pop();
            if cube_track.len() < 10 {
                println!(
                    "Iterated all candidates, now having {}; first placement={:?}",
                    cube_track.len(),
                    cube_track[0].1,
                );
            }
        }
    }

    println!("No solution found");
}
