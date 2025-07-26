#include "chess.hpp"
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>
#include <climits>
#include <chrono>
#include <unordered_map>
#include <thread>
#include <atomic>

using namespace chess;

class UCIChessEngine {
private:

    std::atomic<uint64_t> nodes_searched{0};
    uint64_t tt_hits = 0;

    static constexpr int PIECE_VALUES[6] = {100, 320, 330, 500, 900, 20000};
    
    static constexpr int PAWN_TABLE[64] = {
        0, 0, 0, 0, 0, 0, 0, 0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
        5, 5, 10, 25, 25, 10, 5, 5,
        0, 0, 0, 20, 20, 0, 0, 0,
        5, -5,-10, 0, 0,-10, -5, 5,
        5, 10, 10,-20,-20, 10, 10, 5,
        0, 0, 0, 0, 0, 0, 0, 0
    };
    
    static constexpr int KNIGHT_TABLE[64] = {
        -50,-40,-30,-30,-30,-30,-40,-50,
        -40,-20, 0, 0, 0, 0,-20,-40,
        -30, 0, 10, 15, 15, 10, 0,-30,
        -30, 5, 15, 20, 20, 15, 5,-30,
        -30, 0, 15, 20, 20, 15, 0,-30,
        -30, 5, 10, 15, 15, 10, 5,-30,
        -40,-20, 0, 5, 5, 0,-20,-40,
        -50,-40,-30,-30,-30,-30,-40,-50
    };
    
    static constexpr int BISHOP_TABLE[64] = {
        -20,-10,-10,-10,-10,-10,-10,-20,
        -10, 0, 0, 0, 0, 0, 0,-10,
        -10, 0, 5, 10, 10, 5, 0,-10,
        -10, 5, 5, 10, 10, 5, 5,-10,
        -10, 0, 10, 10, 10, 10, 0,-10,
        -10, 10, 10, 10, 10, 10, 10,-10,
        -10, 5, 0, 0, 0, 0, 5,-10,
        -20,-10,-10,-10,-10,-10,-10,-20
    };
    
    static constexpr int ROOK_TABLE[64] = {
        0, 0, 0, 0, 0, 0, 0, 0,
        5, 10, 10, 10, 10, 10, 10, 5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        -5, 0, 0, 0, 0, 0, 0, -5,
        0, 0, 0, 5, 5, 0, 0, 0
    };
    
    static constexpr int QUEEN_TABLE[64] = {
        -20,-10,-10, -5, -5,-10,-10,-20,
        -10, 0, 0, 0, 0, 0, 0,-10,
        -10, 0, 5, 5, 5, 5, 0,-10,
        -5, 0, 5, 5, 5, 5, 0, -5,
        0, 0, 5, 5, 5, 5, 0, -5,
        -10, 5, 5, 5, 5, 5, 0,-10,
        -10, 0, 5, 0, 0, 0, 0,-10,
        -20,-10,-10, -5, -5,-10,-10,-20
    };
    
    static constexpr int KING_MIDDLE_GAME_TABLE[64] = {
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
        20, 20, 0, 0, 0, 0, 20, 20,
        20, 30, 10, 0, 0, 10, 30, 20
    };
    
    struct TTEntry {
        uint64_t hash; //zobrist hash of the move
        int score;
        int depth;
        int age;
        enum Flag { EXACT, LOWER_BOUND, UPPER_BOUND };
        Flag flag;
        Move best_move;
    };
    
    Board board;
    std::vector<TTEntry> transposition_table;
    int tt_size;
    int tt_age;
    std::atomic<bool> stop_search{false};
    
    // Killer moves and history heuristics
    Move killer_moves[64][2];  // depth, slot
    int history_table[64][64]; 
    
    // defualt UCI Options
    int search_depth = 8;
    int move_time = 50000; // 50 sec
    
public:
    UCIChessEngine() : tt_size(32 * 1048576), tt_age(0) {
        board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        transposition_table.resize(tt_size);
        clearTables();
    }
    
    void clearTables() {
        std::fill(transposition_table.begin(), transposition_table.end(), TTEntry{});
        memset(killer_moves, 0, sizeof(killer_moves));
        memset(history_table, 0, sizeof(history_table));
        tt_age = 0;
    }
    
    int getPieceValue(PieceType piece) const{
        return PIECE_VALUES[static_cast<int>(piece)];}
    
    int getPositionalValue(PieceType piece, Square square, Color color) const {
        int sq = static_cast<int>(square.index());
        if (color == Color::BLACK) {
            sq = 63 - sq;
        }
        
        switch (static_cast<int>(piece)) {
            case static_cast<int>(PieceType::PAWN):   return PAWN_TABLE[sq];
            case static_cast<int>(PieceType::KNIGHT): return KNIGHT_TABLE[sq];
            case static_cast<int>(PieceType::BISHOP): return BISHOP_TABLE[sq];
            case static_cast<int>(PieceType::ROOK):   return ROOK_TABLE[sq];
            case static_cast<int>(PieceType::QUEEN):  return QUEEN_TABLE[sq];
            case static_cast<int>(PieceType::KING):   return KING_MIDDLE_GAME_TABLE[sq];
            default: return 0;
        }
    }
    
    int evaluate(const Board& board) {
        // gameover?
        auto gameResult = board.isGameOver();
        GameResultReason result = gameResult.first;
        
        if (result != GameResultReason::NONE) {
            if (result == GameResultReason::CHECKMATE) {
                return board.sideToMove() == Color::WHITE ? -30000 : 30000; //win scores
            }
            return 0; //draw
        }
        
        int score = 0;
        
        //positional evaluation
        for (int sq = 0; sq < 64; sq++) {
            Square square = Square(sq);
            Piece piece = board.at(square);
            
            if (piece == Piece::NONE) continue;
            
            PieceType pieceType = piece.type();
            Color pieceColor = piece.color();
            
            int pieceValue = getPieceValue(pieceType);
            int positionalValue = getPositionalValue(pieceType, square, pieceColor);
            
            int totalValue = pieceValue + positionalValue;
            
            if (pieceColor == Color::WHITE) {
                score += totalValue;
            } else {
                score -= totalValue;
            }
        }
        
        if (board.inCheck()) {
            score -= 430;
        }
        
        return score;
    }
    
    int mvvLvaScore(const Move& move, const Board& board) { // faster method of checking if move moved loses or wins material value

        Piece victim = board.at(move.to());
        Piece attacker = board.at(move.from());

        if (victim == Piece::NONE) return 0;

        return getPieceValue(victim.type()) * 10 - getPieceValue(attacker.type());
    }
    
    void orderMoves(Movelist& moves, const Board& board, int depth, Move tt_move = Move::NULL_MOVE) {
        if (moves.empty()) return;
        
        std::vector<std::pair<int, Move>> move_scores;
        move_scores.reserve(moves.size());
        
        for (const Move& move : moves) {
            int score = 0;
            
            if (move == tt_move) {
                score = 1000000;
            }
            else if (board.at(move.to()) != Piece::NONE) {
                score = 100000 + mvvLvaScore(move, board);
            }
            else if (move == killer_moves[depth][0]) {
                score = 90000;
            }
            else if (move == killer_moves[depth][1]) {
                score = 80000;
            }
            else {
                score = history_table[move.from().index()][move.to().index()];
            }
            move_scores.emplace_back(score, move);
        }
        
        // Sorting moves by scores
        std::sort(move_scores.begin(), move_scores.end(), []( auto& a, auto& b) { return a.first > b.first; });
        
        // we Create a new temporary movelist and copy it back
        std::vector<Move> sorted_moves;
        sorted_moves.reserve(move_scores.size());
        for (const auto& pair : move_scores) {
            sorted_moves.push_back(pair.second);
        }
        for (size_t i = 0; i < sorted_moves.size() && i < moves.size(); i++) {
            moves[i] = sorted_moves[i];
        }
    }
    
    void storeTT(uint64_t hash, int score, int depth, TTEntry::Flag flag, Move best_move) {
        int index = hash % tt_size;
        TTEntry& entry = transposition_table[index];
        
        // we replace the entry if it is : empty or same position or deeper search or older entry
        if (entry.hash == 0 || entry.hash == hash || 
            depth >= entry.depth || entry.age < tt_age) {
            entry.hash = hash;
            entry.score = score;
            entry.depth = depth;
            entry.flag = flag;
            entry.best_move = best_move;
            entry.age = tt_age;
        }
    }
    // checking if our transposition table has entry required
    bool probeTT(uint64_t hash, int& score, int depth, int alpha, int beta, Move& best_move) {
        int index = hash % tt_size;
        const TTEntry& entry = transposition_table[index];
        
        if (entry.hash == hash && entry.depth >= depth) {

            tt_hits++;

            best_move = entry.best_move;
            
            if (entry.flag == TTEntry::EXACT) {
                score = entry.score;
                return true;
            }
            else if (entry.flag == TTEntry::LOWER_BOUND && entry.score >= beta) {
                score = entry.score;
                return true;
            }
            else if (entry.flag == TTEntry::UPPER_BOUND && entry.score <= alpha) {
                score = entry.score;
                return true;
            }
        }
        
        if (entry.hash == hash) {
            best_move = entry.best_move;
        }
        
        return false;
    }
    
    int alphaBeta(Board& board, int depth, int alpha, int beta, bool maximizing, std::chrono::steady_clock::time_point start_time, int time_limit, int ply = 0) {
        nodes_searched.fetch_add(1);

        if (stop_search.load()) {
            return evaluate(board);
        }
        

    
        auto gameResult = board.isGameOver();
        GameResultReason result = gameResult.first;
        if (result != GameResultReason::NONE) {
            if (result == GameResultReason::CHECKMATE) {
                return board.sideToMove() == Color::WHITE ? -30000 + ply : 30000 - ply;
            }
            return 0;
        }
        
        if (depth == 0) {
            return evaluate(board);
        }
        
        uint64_t hash = board.hash();
        Move tt_move = Move::NULL_MOVE;
        int tt_score;
        
        if (probeTT(hash, tt_score, depth, alpha, beta, tt_move)) {
            return tt_score;
        }
        
        Movelist moves;
        movegen::legalmoves(moves, board);
        orderMoves(moves, board, ply, tt_move);
        
        int bestValue = maximizing ? INT_MIN : INT_MAX;
        Move bestMove = Move::NULL_MOVE;
        TTEntry::Flag flag = TTEntry::UPPER_BOUND;
        
        for (size_t i = 0; i < moves.size(); i++) {
            const Move& move = moves[i];
            
            if (stop_search.load()) break;
            

            if (true) {
                auto current_time = std::chrono::steady_clock::now();
                auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
                if (elapsed.count() > time_limit) {
                    stop_search.store(true);
                    break;
                }
            }


            board.makeMove(move);
            int value = alphaBeta(board, depth - 1, alpha, beta, !maximizing, start_time, time_limit, ply + 1);
            board.unmakeMove(move);
            
            if (maximizing) {
                if (value > bestValue) {
                    bestValue = value;
                    bestMove = move;
                }
                alpha = std::max(alpha, bestValue);
                
                if (beta <= alpha) {
                    if (board.at(move.to()) == Piece::NONE) { 
                        if (killer_moves[ply][0] != move) {
                            killer_moves[ply][1] = killer_moves[ply][0];
                            killer_moves[ply][0] = move;
                        }
                        
                        // Update history table
                        history_table[move.from().index()][move.to().index()] += depth * depth;
                    }
                    flag = TTEntry::LOWER_BOUND;
                    break;
                }
            } else {
                if (value < bestValue) {
                    bestValue = value;
                    bestMove = move;
                }
                beta = std::min(beta, bestValue);
                
                if (beta <= alpha) {
                    if (board.at(move.to()) == Piece::NONE) { 
                        if (killer_moves[ply][0] != move) {
                            killer_moves[ply][1] = killer_moves[ply][0];
                            killer_moves[ply][0] = move;
                        }
                        
                        // Update history table
                        history_table[move.from().index()][move.to().index()] += depth * depth;
                    }
                    flag = TTEntry::LOWER_BOUND;
                    break;
                }
            }
        }
        
        if (bestValue > alpha && bestValue < beta) {
            flag = TTEntry::EXACT;
        }
        
        if (!stop_search.load()) {
            storeTT(hash, bestValue, depth, flag, bestMove);
        }
        
        return bestValue;
    }
    
    Move findBestMove(int max_depth, int time_limit) {
        
        stop_search.store(false);
        tt_age++;

        nodes_searched.store(0);
        tt_hits = 0;  
        
        auto start_time = std::chrono::steady_clock::now();
        
        Movelist moves;
        movegen::legalmoves(moves, board);
        
        if (moves.empty()) {
            return Move::NULL_MOVE;
        }
        
        Move bestMove = moves[0];
        int bestValue = (board.sideToMove() == Color::WHITE) ? INT_MIN : INT_MAX;
        bool maximizing = (board.sideToMove() == Color::WHITE);
        
        // Clear killer moves and history for new search
        memset(killer_moves, 0, sizeof(killer_moves));
        
        // Starting from depth 6 since it takes very less time and only search even depths since odd ones result in bad moves
        int start_depth = 6;
        
        for (int d = start_depth; d <= max_depth && !stop_search.load(); d += 2) {
            auto current_time = std::chrono::steady_clock::now();
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
            
            // Check if we have enough time to reasonably complete this depth, here factor of 25 per each depth has been chosen
            //expecting each depth to take atleast 14 times the time taken by previous depth
            if (elapsed.count() > time_limit * 0.07) {
                break;
            }
            
            int currentBestValue = maximizing ? INT_MIN : INT_MAX;
            Move currentBestMove = bestMove;  // Use previous best move as fallback in case incomplete search due to time constraints
            bool depth_completed = true;
            
            int alpha = INT_MIN, beta = INT_MAX;
            
            for (const Move& move : moves) {
                if (stop_search.load()) {
                    depth_completed = false;
                    break;
                }
                
                board.makeMove(move);
                int value = alphaBeta(board, d - 1, alpha, beta, !maximizing, start_time, time_limit);
                board.unmakeMove(move);
                
                if (stop_search.load()) {
                    depth_completed = false;
                    break;
                }
                
                if ((maximizing && value > currentBestValue) || (!maximizing && value < currentBestValue)) {
                    currentBestValue = value;
                    currentBestMove = move;
                    
                    // Update alpha-beta
                    if (maximizing) {
                        alpha = std::max(alpha, value);
                    } else {
                        beta = std::min(beta, value);
                    }
                }
            }
            
            // Only update best move/value if we completed the depth entirely to prevent blunders
            if (depth_completed && !stop_search.load()) {
                bestValue = currentBestValue;
                bestMove = currentBestMove;
                
                auto current_time = std::chrono::steady_clock::now();
                auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
                
                uint64_t nodes = nodes_searched.load();
                uint64_t nps = elapsed.count() > 0 ? (nodes * 1000) / elapsed.count() : 0;
                int hashfull = (tt_hits * 1000) / std::max(nodes, 1ULL);
                
                std::cout << "info depth " << d 
                        << " score cp " << bestValue 
                        << " time " << elapsed.count()
                        << " nodes " << nodes
                        << " nps " << nps
                        << " hashfull " << hashfull
                        << " pv " << uci::moveToUci(bestMove) << std::endl;
            }
        }
        
        return bestMove;
    }
    
    // UCI  Implementation
    void uci_loop() {
        std::string line;
        
        while (std::getline(std::cin, line)) {
            std::istringstream iss(line);
            std::string command;
            iss >> command;
            
            if (command == "quit") {
                break;
            }
            else if (command == "uci") {
                std::cout << "option name Depth type spin default 16 min 6 max 20\n";
                std::cout << "option name MoveTime type spin default 60000 min 100 max 300000\n";
                std::cout << "uciok\n";
            }
            else if (command == "isready") {
                std::cout << "readyok\n";
            }
            else if (command == "ucinewgame") {
                board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
                clearTables();
            }
            else if (command == "position") {
                std::string subcommand;
                iss >> subcommand;
                
                if (subcommand == "startpos") {
                    board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
                    
                    // Check for moves after startpos
                    std::string moves_token;
                    if (iss >> moves_token && moves_token == "moves") {
                        std::string move_str;
                        while (iss >> move_str) {
                            Move move = uci::uciToMove(board, move_str);
                            board.makeMove(move);
                        }
                    }
                }
                else if (subcommand == "fen") {
                    std::string fen;
                    std::string word;
                    
                    // Read FEN string
                    for (int i = 0; i < 6 && iss >> word && word != "moves"; i++) {
                        if (!fen.empty()) fen += " ";
                        fen += word;
                    }
                    
                    board.setFen(fen);
                    

                    if (word == "moves") {
                        std::string move_str;
                        while (iss >> move_str) {
                            Move move = uci::uciToMove(board, move_str);
                            board.makeMove(move);
                        }
                    }
                }
            }
            else if (command == "go") {
                int depth = search_depth;
                int movetime = move_time;
                int wtime = 0, btime = 0, winc = 0, binc = 0;
                
                std::string param;
                while (iss >> param) {
                    if (param == "depth") {
                        iss >> depth;
                    }
                    else if (param == "movetime") {
                        iss >> movetime;
                    }
                    else if (param == "wtime") {
                        iss >> wtime;
                    }
                    else if (param == "btime") {
                        iss >> btime;
                    }
                    else if (param == "winc") {
                        iss >> winc;
                    }
                    else if (param == "binc") {
                        iss >> binc;
                    }
                }
                
                //  time calculation
                int time_limit = movetime;
                if (wtime > 0 || btime > 0) {
                    int my_time = (board.sideToMove() == Color::WHITE) ? wtime : btime;
                    int my_inc = (board.sideToMove() == Color::WHITE) ? winc : binc;
                    time_limit = std::min(my_time/4 + my_inc, move_time);
                }
                time_limit = std::max(time_limit, 50);
                
                Move bestMove = findBestMove(depth, time_limit);
                if (bestMove != Move::NULL_MOVE) {
                    std::cout << "bestmove " << uci::moveToUci(bestMove) << std::endl;
                } else {
                    Movelist moves;
                    movegen::legalmoves(moves, board);
                    if (!moves.empty()) {
                        std::cout << "bestmove " << uci::moveToUci(moves[0]) << std::endl;
                    } else {
                        std::cout << "bestmove 0000" << std::endl;
                    }
                }
            }
            else if (command == "stop") {
                stop_search.store(true);
            }
            else if (command == "setoption") {
                std::string name_token, name, value_token, value;
                iss >> name_token >> name >> value_token >> value;
                
                if (name == "Depth") {
                    search_depth = std::stoi(value);
                }
                else if (name == "MoveTime") {
                    move_time = std::stoi(value);
                }
            }
            
            std::cout.flush();
        }
    }
};

int main() {
    UCIChessEngine engine;
    engine.uci_loop();
    return 0;
}