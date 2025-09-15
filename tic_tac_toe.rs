use std::io;

#[derive(Clone, Copy, PartialEq)]
enum Cell {
    Empty,
    X,
    O,
}

impl Cell {
    fn symbol(&self) -> &'static str {
        match self {
            Cell::Empty => ".",
            Cell::X => "X",
            Cell::O => "O",
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
enum Player {
    X,
    O,
}

impl Player {
    fn to_cell(&self) -> Cell {
        match self {
            Player::X => Cell::X,
            Player::O => Cell::O,
        }
    }

    fn opponent(&self) -> Player {
        match self {
            Player::X => Player::O,
            Player::O => Player::X,
        }
    }
}

#[derive(Clone)]
struct Board {
    cells: Vec<Cell>, // length 9
}

impl Board {
    fn new() -> Self {
        Self {
            cells: vec![Cell::Empty; 9],
        }
    }

    fn print(&self) {
        for r in 0..3 {
            for c in 0..3 {
                print!("{} ", self.cells[r * 3 + c].symbol());
            }
            println!();
        }
        println!();
    }

    fn is_full(&self) -> bool {
        self.cells.iter().all(|&c| c != Cell::Empty)
    }

    fn winner(&self) -> Option<Player> {
        let lines = [
            (0, 1, 2),
            (3, 4, 5),
            (6, 7, 8),
            (0, 3, 6),
            (1, 4, 7),
            (2, 5, 8),
            (0, 4, 8),
            (2, 4, 6),
        ];

        for &(a, b, c) in &lines {
            if self.cells[a] != Cell::Empty
                && self.cells[a] == self.cells[b]
                && self.cells[b] == self.cells[c]
            {
                return match self.cells[a] {
                    Cell::X => Some(Player::X),
                    Cell::O => Some(Player::O),
                    _ => None,
                };
            }
        }
        None
    }

    fn play(&mut self, idx: usize, player: Player) {
        self.cells[idx] = player.to_cell();
    }

    fn undo(&mut self, idx: usize) {
        self.cells[idx] = Cell::Empty;
    }

    fn available_moves(&self) -> Vec<usize> {
        self.cells
            .iter()
            .enumerate()
            .filter_map(|(i, &c)| if c == Cell::Empty { Some(i) } else { None })
            .collect()
    }
}

/// Negamax search
fn negamax(board: &mut Board, player: Player) -> i8 {
    if let Some(winner) = board.winner() {
        return if winner == player { 1 } else { -1 };
    }
    if board.is_full() {
        return 0;
    }

    let mut best = i8::MIN + 1;
    for mv in board.available_moves() {
        board.play(mv, player);
        let score = -negamax(board, player.opponent());
        board.undo(mv);
        if score > best {
            best = score;
            if best == 1 {
                return best;
            }
        }
    }
    best
}

fn best_move(board: &mut Board, player: Player) -> Option<usize> {
    let mut best_score = i8::MIN + 1;
    let mut best_mv = None;

    for mv in board.available_moves() {
        board.play(mv, player);
        let score = -negamax(board, player.opponent());
        board.undo(mv);
        if score > best_score {
            best_score = score;
            best_mv = Some(mv);
        }
    }

    best_mv
}

fn main() {
    let mut board = Board::new();
    let human = Player::X;
    let engine = Player::O;
    let mut current = Player::X;

    println!("You are X (0-8 positions). Engine is O.");
    println!("Board positions are:");
    println!("0 1 2\n3 4 5\n6 7 8\n");
    board.print();

    loop {
        if let Some(w) = board.winner() {
            println!("Game over! Winner: {}", w.to_cell().symbol());
            break;
        }
        if board.is_full() {
            println!("Game over! Draw.");
            break;
        }

        if current == human {
            // Human turn
            loop {
                println!("Enter your move (0-8): ");
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                if let Ok(idx) = input.trim().parse::<usize>() {
                    if idx < 9 && board.cells[idx] == Cell::Empty {
                        board.play(idx, human);
                        break;
                    }
                }
                println!("Invalid move, try again.");
            }
        } else {
            // Engine turn
            if let Some(mv) = best_move(&mut board, engine) {
                println!("Engine plays at {}", mv);
                board.play(mv, engine);
            }
        }

        board.print();
        current = current.opponent();
    }
}
