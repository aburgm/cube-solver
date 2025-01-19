use cube_solver::{Solver, State};

fn main() {
    let solver = Solver::new();
    let mut cube_track: Vec<State> = vec![Default::default()];

    while !cube_track.is_empty() {
        let len = cube_track.len();
        if let Some(new_state) = solver.next_candidate(&mut cube_track[len - 1]) {
            if Solver::is_complete(&new_state) {
                // we found a winner
                println!("We found a solution!");
                return;
            }
            // If new candidate is final state, we can return
            cube_track.push(new_state);
            if cube_track.len() < 10 {
                println!(
                    "Found a new candidate, now having {}; first level next piece={:?}",
                    cube_track.len(),
                    solver.next_piece(&cube_track[0]),
                );
            }
        } else {
            cube_track.pop();
            if cube_track.len() < 10 {
                println!(
                    "Iterated all candidates, now having {}; first level next piece={:?}",
                    cube_track.len(),
                    solver.next_piece(&cube_track[0]),
                );
            }
        }
    }

    println!("No solution found");
}
