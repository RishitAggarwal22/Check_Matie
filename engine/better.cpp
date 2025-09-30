// upv3_fixed.cpp  (modified to work with disservin chess.hpp)
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
#include <fstream>
#include <random>
#include <cmath>
#include <cstring> // for memset

// Optional: Include Fathom for Syzygy support
extern "C" {
#include "Fathom/src/tbprobe.h"
}

// --- Fathom compatibility shims (some builds miss these macros) ---
#ifndef TB_GET_FROM
#   define TB_GET_FROM(m)        (int)(((m) >> 6) & 0x3F)
#endif
#ifndef TB_GET_TO
#   define TB_GET_TO(m)          (int)((m) & 0x3F)
#endif
// Promotion: 0 = none, 1 = N, 2 = B, 3 = R, 4 = Q
#if !defined(TB_GET_PROMOTION) && defined(TB_PROMOTES)
#   define TB_GET_PROMOTION(m)   TB_PROMOTES(m)
#elif !defined(TB_GET_PROMOTION)
#   define TB_GET_PROMOTION(m)   (int)(((m) >> 12) & 0x7)
#endif
#ifndef TB_MOVE_NONE
#   define TB_MOVE_NONE 0u
#endif




using namespace chess;

class UCIChessEngine {
private:
    // Enhanced evaluation constants
    static constexpr int PIECE_VALUES[6] = {100, 320, 330, 500, 900, 20000};
    
    // (piece-square tables omitted here for brevity — unchanged)
    static constexpr int PAWN_TABLE_MG[64] = {
        0, 0, 0, 0, 0, 0, 0, 0,
        50, 50, 50, 50, 50, 50, 50, 50,
        10, 10, 20, 30, 30, 20, 10, 10,
        5, 5, 10, 25, 25, 10, 5, 5,
        0, 0, 0, 20, 20, 0, 0, 0,
        5, -5,-10, 0, 0,-10, -5, 5,
        5, 10, 10,-20,-20, 10, 10, 5,
        0, 0, 0, 0, 0, 0, 0, 0
    };
    static constexpr int PAWN_TABLE_EG[64] = {
        0, 0, 0, 0, 0, 0, 0, 0,
        80, 80, 80, 80, 80, 80, 80, 80,
        50, 50, 50, 50, 50, 50, 50, 50,
        30, 30, 30, 30, 30, 30, 30, 30,
        20, 20, 20, 20, 20, 20, 20, 20,
        10, 10, 10, 10, 10, 10, 10, 10,
        10, 10, 10, 10, 10, 10, 10, 10,
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
    static constexpr int KING_MG_TABLE[64] = {
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -30,-40,-40,-50,-50,-40,-40,-30,
        -20,-30,-30,-40,-40,-30,-30,-20,
        -10,-20,-20,-20,-20,-20,-20,-10,
        20, 20, 0, 0, 0, 0, 20, 20,
        20, 30, 10, 0, 0, 10, 30, 20
    };
    static constexpr int KING_EG_TABLE[64] = {
        -50,-40,-30,-20,-20,-30,-40,-50,
        -30,-20,-10, 0, 0,-10,-20,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 30, 40, 40, 30,-10,-30,
        -30,-10, 20, 30, 30, 20,-10,-30,
        -30,-30, 0, 0, 0, 0,-30,-30,
        -50,-30,-30,-30,-30,-30,-30,-50
    };
    
    // Safe infinity constant for search (avoid INT_MIN/INT_MAX UB).
    static constexpr int INF = 30000;
    static constexpr int NEG_INF = -INF;

    // Transposition Table Entry
    struct TTEntry {
        uint64_t hash{0};
        int score{0};
        int depth{0};
        int age{0};
        enum Flag { EXACT, LOWER_BOUND, UPPER_BOUND };
        Flag flag{UPPER_BOUND};
        Move best_move{Move::NULL_MOVE};
    };
    
    // Opening Book Structure
    struct BookEntry {
        std::string position_fen;
        std::vector<std::pair<std::string, int>> moves; // move and weight
    };
    
    // PV (Principal Variation) Table
    struct PVTable {
        Move pv[64][64]; // [ply][index]
        int pv_length[64];
        
        void clear() {
            memset(pv, 0, sizeof(pv));
            memset(pv_length, 0, sizeof(pv_length));
        }
    };
    
    Board board;
    std::vector<TTEntry> transposition_table;
    PVTable pv_table;
    int tt_size;
    int tt_age;
    
    // Search control
    std::atomic<bool> stop_search{false};
    std::atomic<uint64_t> nodes_searched{0};
    uint64_t tt_hits = 0;
    
    // Move ordering heuristics
    Move killer_moves[64][2];
    int history_table[64][64];
    Move counter_moves[64][64]; // [from][to] -> counter move
    
    // Opening book
    std::unordered_map<std::string, std::vector<std::pair<std::string, int>>> opening_book;
    bool use_book = true;
    int book_depth_limit = 15; // Use book up to move 15
    
    // Evaluation cache
    struct EvalCacheEntry {
        uint64_t hash{0};
        int score{0};
    };
    std::vector<EvalCacheEntry> eval_cache;
    static constexpr int EVAL_CACHE_SIZE = 65536;
    
    // UCI Options
    int search_depth = 30;
    int move_time = 75000;
    bool use_syzygy = false;
    std::string syzygy_path = "";
    
    // Random number generator for book moves (seed cast to uint32_t to avoid narrowing)
    std::mt19937 rng{ static_cast<uint32_t>(
        std::chrono::steady_clock::now().time_since_epoch().count()
    )};
    
    // Track move stack because disservin::Board doesn't provide lastMove()
    std::vector<Move> move_stack;
    
    // --- Helpers for working with Bitboard and board move tracking ---
    static inline int popcount(const Bitboard& b) {
        return __builtin_popcountll(b.getBits());
    }
    
    // Pop least-significant set bit and return corresponding Square
    static inline Square pop_lsb(Bitboard &b) {
        uint64_t bits = b.getBits();
        if (bits == 0) return Square::NO_SQ; // defensive guard
        int idx = __builtin_ctzll(bits);
        uint64_t newbits = bits & (bits - 1);
        b = Bitboard(newbits);
        return Square(idx);
    }
    
    inline Move lastMoveOnBoard() const {
        if (move_stack.empty()) return Move::NULL_MOVE;
        return move_stack.back();
    }
    
    inline void makeMoveOnBoard(const Move &m) {
        board.makeMove(m);
        move_stack.push_back(m);
    }
    
    inline void unmakeMoveOnBoard(const Move &m) {
        // Unmake on board first, then pop the recorded move
        board.unmakeMove(m);
        if (!move_stack.empty()) move_stack.pop_back();
    }
    
    inline void makeNullMoveOnBoard() {
        board.makeNullMove();
        move_stack.push_back(Move::NULL_MOVE);
    }
    
    inline void unmakeNullMoveOnBoard() {
        // Unmake null move on board first, then pop the stack entry
        board.unmakeMove(Move::NULL_MOVE);
        if (!move_stack.empty()) move_stack.pop_back();
    }

    inline std::string normalizeFenForBook(const std::string &fen) {
        std::istringstream iss(fen);
        std::string part1, part2, part3, part4;
        if (!(iss >> part1)) return fen;
        if (!(iss >> part2)) part2 = "w";
        if (!(iss >> part3)) part3 = "-";
        if (!(iss >> part4)) part4 = "-";
        return part1 + " " + part2 + " " + part3 + " " + part4;
    }

    inline bool isEndgamePosition(const Board &b) {
        // Simple material threshold. King's value large, so only include minors+majors+pawns
        int material = 0;
        // weights approximate pawns=100, knight=320, bishop=330, rook=500, queen=900
        material += popcount(b.pieces(PieceType::PAWN, Color::WHITE)) * PIECE_VALUES[0];
        material += popcount(b.pieces(PieceType::PAWN, Color::BLACK)) * PIECE_VALUES[0];
        material += popcount(b.pieces(PieceType::KNIGHT)) * PIECE_VALUES[1];
        material += popcount(b.pieces(PieceType::BISHOP)) * PIECE_VALUES[2];
        material += popcount(b.pieces(PieceType::ROOK)) * PIECE_VALUES[3];
        material += popcount(b.pieces(PieceType::QUEEN)) * PIECE_VALUES[4];

        // If total (both sides combined) material <= 2400 -> endgame.
        // Tuneable threshold: 2400 corresponds roughly to queen + a few pieces remaining.
        return material <= 2400;
    }


    
public:
    UCIChessEngine() : tt_size(64 * 1048576), tt_age(0) {
        board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        transposition_table.resize(tt_size);
        eval_cache.resize(EVAL_CACHE_SIZE);
        clearTables();
        loadOpeningBook();
        // do not init syzygy until user sets path
        // initSyzygy();
    }
    
    ~UCIChessEngine() {
        // Clean up Syzygy if initialized
        // if (use_syzygy) tb_free();  // depending on Fathom build
    }
    
    void clearTables() {
        // Reset TT and various heuristics
        for (auto &e : transposition_table) e = TTEntry{};
        for (auto &e : eval_cache) e = EvalCacheEntry{};
        memset(killer_moves, 0, sizeof(killer_moves));
        memset(history_table, 0, sizeof(history_table));
        memset(counter_moves, 0, sizeof(counter_moves));
        pv_table.clear();
        tt_age = 0;
    }
    
    void loadOpeningBook() {
        // (unchanged — book lines)
        addBookLine("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", "e2e4", 100);
        addBookLine("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1", "e7e5", 90);
        addBookLine("rnbqkb1r/pppp1ppp/5n2/4p3/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2", "g1f3", 85);
        addBookLine("r1bqkb1r/pppp1ppp/2n2n2/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R w KQkq - 0 3", "f1c4", 80);
        // ... (rest of the book lines unchanged)
        addBookLine("rnbqkbnr/ppp1pppp/8/3p4/3P4/8/PPP1PPPP/RNBQKBNR w KQkq - 0 2", "c2c4", 80);
        addBookLine("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1", "c7c5", 85);
        addBookLine("rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2", "g1f3", 80);
        addBookLine("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1", "e7e6", 70);
        addBookLine("rnbqkbnr/pppp1ppp/4p3/8/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2", "d2d4", 75);
        addBookLine("rnbqkbnr/pppppppp/8/8/4P3/8/PPPP1PPP/RNBQKBNR b KQkq - 0 1", "c7c6", 65);
        addBookLine("rnbqkbnr/pp1ppppp/2p5/8/4P3/8/PPPP1PPP/RNBQKBNR w KQkq - 0 2", "d2d4", 70);
        addBookLine("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", "c2c4", 70);
        addBookLine("rnbqkbnr/pppppppp/8/8/2P5/8/PP1PPPPP/RNBQKBNR b KQkq - 0 1", "e7e5", 65);
        addBookLine("rnbqkbnr/pppppppp/8/8/3P4/8/PPP1PPPP/RNBQKBNR b KQkq - 0 1", "g8f6", 75);
        addBookLine("rnbqkb1r/pppppppp/5n2/8/3P4/8/PPP1PPPP/RNBQKBNR w KQkq - 0 2", "c2c4", 70);
        addBookLine("rnbqkb1r/pppppppp/5n2/8/2PP4/8/PP2PPPP/RNBQKBNR b KQkq - 0 2", "g7g6", 65);
    }
    
    void addBookLine(const std::string& fen, const std::string& move, int weight) {
        opening_book[fen].push_back({move, weight});
    }
    
    Move getBookMove() {
        if (!use_book) return Move::NULL_MOVE;

        // book_depth_limit is in full moves (1..N). We use move_stack size to count plies.
        int played_full_moves = static_cast<int>(move_stack.size() / 2);
        if (played_full_moves >= book_depth_limit) return Move::NULL_MOVE;

        // Use normalized FEN (ignore halfmove/fullmove counters) to increase hit-rate.
        std::string raw_fen = board.getFen();
        std::string key = normalizeFenForBook(raw_fen);

        auto it = opening_book.find(key);
        if (it == opening_book.end()) return Move::NULL_MOVE;

        // Weighted selection but prefer top moves more often: pick with softmax-ish bias.
        const auto &entries = it->second;
        if (entries.empty()) return Move::NULL_MOVE;

        // compute total weight and track best
        int total_weight = 0;
        int best_weight = -1; size_t best_idx = 0;
        for (size_t i = 0; i < entries.size(); ++i) {
            int w = std::max(1, entries[i].second);
            total_weight += w;
            if (w > best_weight) { best_weight = w; best_idx = i; }
        }

        // With some probability (e.g., 60%) pick the highest-weight move,
        // otherwise do weighted random among all moves (adds variety).
        std::uniform_int_distribution<int> pickBestDist(0, 99);
        int pickBestChance = 60;
        if (pickBestDist(rng) < pickBestChance) {
            // try to convert best move string to a Move (guard)
            Move m = Move::NULL_MOVE;
            try {
                m = uci::uciToMove(board, entries[best_idx].first);
            } catch (...) { m = Move::NULL_MOVE; }
            if (m != Move::NULL_MOVE) return m;
            // fallback to weighted random if conversion fails
        }

        std::uniform_int_distribution<int> dist(0, total_weight - 1);
        int r = dist(rng);
        int cum = 0;
        for (const auto &p : entries) {
            cum += std::max(1, p.second);
            if (r < cum) {
                try {
                    return uci::uciToMove(board, p.first);
                } catch (...) {
                    return Move::NULL_MOVE;
                }
            }
        }

        return Move::NULL_MOVE;
    }
    
    void initSyzygy() {
        if (syzygy_path.empty()) return;
        int success = tb_init(syzygy_path.c_str());
        if (success == 0) {
            std::cerr << "info string Syzygy path invalid: " << syzygy_path << std::endl;
            use_syzygy = false;
        } else {
            std::cout << "info string Syzygy initialized at " << syzygy_path << std::endl;
            use_syzygy = true;
        }
    }

    
    Move probeSyzygyMove(int &scoreOut) {
        scoreOut = INT_MIN;
        if (!use_syzygy) return Move::NULL_MOVE;

        unsigned results[TB_MAX_MOVES];
        unsigned result = tb_probe_root(
            (board.pieces(PieceType::PAWN, Color::WHITE)   |
            board.pieces(PieceType::KNIGHT, Color::WHITE) |
            board.pieces(PieceType::BISHOP, Color::WHITE) |
            board.pieces(PieceType::ROOK, Color::WHITE)   |
            board.pieces(PieceType::QUEEN, Color::WHITE)  |
            board.pieces(PieceType::KING, Color::WHITE)).getBits(),

            (board.pieces(PieceType::PAWN, Color::BLACK)   |
            board.pieces(PieceType::KNIGHT, Color::BLACK) |
            board.pieces(PieceType::BISHOP, Color::BLACK) |
            board.pieces(PieceType::ROOK, Color::BLACK)   |
            board.pieces(PieceType::QUEEN, Color::BLACK)  |
            board.pieces(PieceType::KING, Color::BLACK)).getBits(),

            board.pieces(PieceType::KING).getBits(),
            board.pieces(PieceType::QUEEN).getBits(),
            board.pieces(PieceType::ROOK).getBits(),
            board.pieces(PieceType::BISHOP).getBits(),
            board.pieces(PieceType::KNIGHT).getBits(),
            board.pieces(PieceType::PAWN).getBits(),
            board.halfMoveClock(),
            0,
            (board.enpassantSq() != Square::NO_SQ) ? board.enpassantSq().index() : 0,
            board.sideToMove() == Color::WHITE,
            results
        );

        if (result == TB_RESULT_FAILED) return Move::NULL_MOVE;
        if (results[0] == TB_MOVE_NONE) return Move::NULL_MOVE;

        // Score (WDL)
        if (TB_GET_WDL(result) == TB_WIN)  scoreOut = 30000;
        else if (TB_GET_WDL(result) == TB_LOSS) scoreOut = -30000;
        else if (TB_GET_WDL(result) == TB_DRAW) scoreOut = 0;

        unsigned best = results[0];
        int from  = TB_GET_FROM(best);
        int to    = TB_GET_TO(best);
        int promo = TB_GET_PROMOTION(best);  // works across Fathom variants

        PieceType promoType = PieceType::NONE;
        switch (promo) {
            case 1: promoType = PieceType::KNIGHT; break;
            case 2: promoType = PieceType::BISHOP; break;
            case 3: promoType = PieceType::ROOK;   break;
            case 4: promoType = PieceType::QUEEN;  break;
        }

        // If you construct moves explicitly:
        Move syzygyMove = Move::make(Square(from), Square(to), promoType);
        return syzygyMove;
    }


    
    int getGamePhase(const Board& b) {
        // Calculate game phase for evaluation interpolation
        int phase = 0;
        phase += popcount(b.pieces(PieceType::KNIGHT)) * 1;
        phase += popcount(b.pieces(PieceType::BISHOP)) * 1;
        phase += popcount(b.pieces(PieceType::ROOK)) * 2;
        phase += popcount(b.pieces(PieceType::QUEEN)) * 4;
        return std::min(phase, 24); // Max phase = 24
    }
    
    int getPositionalValue(PieceType piece, Square square, Color color, int game_phase) const {
        int sq = static_cast<int>(square.index());
        if (color == Color::BLACK) {
            sq = 63 - sq;
        }
        
        int mg_value = 0, eg_value = 0;
        
        switch (static_cast<int>(piece)) {
            case static_cast<int>(PieceType::PAWN):
                mg_value = PAWN_TABLE_MG[sq];
                eg_value = PAWN_TABLE_EG[sq];
                break;
            case static_cast<int>(PieceType::KNIGHT):
                mg_value = KNIGHT_TABLE[sq];
                eg_value = KNIGHT_TABLE[sq] - 10; // Knights slightly worse in endgame
                break;
            case static_cast<int>(PieceType::BISHOP):
                mg_value = BISHOP_TABLE[sq];
                eg_value = BISHOP_TABLE[sq] + 10; // Bishops slightly better in endgame
                break;
            case static_cast<int>(PieceType::ROOK):
                mg_value = ROOK_TABLE[sq];
                eg_value = ROOK_TABLE[sq];
                break;
            case static_cast<int>(PieceType::QUEEN):
                mg_value = QUEEN_TABLE[sq];
                eg_value = QUEEN_TABLE[sq];
                break;
            case static_cast<int>(PieceType::KING):
                mg_value = KING_MG_TABLE[sq];
                eg_value = KING_EG_TABLE[sq];
                break;
        }
        
        // Interpolate based on game phase
        return (mg_value * game_phase + eg_value * (24 - game_phase)) / 24;
    }
    
    int evaluatePawnStructure(const Board& board) {
        int score = 0;

        Bitboard white_pawns = board.pieces(PieceType::PAWN, Color::WHITE);
        Bitboard black_pawns = board.pieces(PieceType::PAWN, Color::BLACK);

        // Doubled pawns penalty (same as before)
        for (int file = 0; file < 8; file++) {
            Bitboard file_mask = Bitboard(0x0101010101010101ULL << file);
            int white_pawns_on_file = popcount(white_pawns & file_mask);
            int black_pawns_on_file = popcount(black_pawns & file_mask);

            if (white_pawns_on_file > 1) score -= 15 * (white_pawns_on_file - 1);
            if (black_pawns_on_file > 1) score += 15 * (black_pawns_on_file - 1);
        }

        // Isolated pawns penalty
        for (int file = 0; file < 8; file++) {
            Bitboard file_mask = Bitboard(0x0101010101010101ULL << file);
            Bitboard adjacent_files = Bitboard(0);
            if (file > 0) adjacent_files |= Bitboard(0x0101010101010101ULL << (file - 1));
            if (file < 7) adjacent_files |= Bitboard(0x0101010101010101ULL << (file + 1));

            if ((white_pawns & file_mask).getBits() && !(white_pawns & adjacent_files).getBits()) {
                score -= 20;
            }
            if ((black_pawns & file_mask).getBits() && !(black_pawns & adjacent_files).getBits()) {
                score += 20;
            }
        }

        // Passed pawn scoring: stronger, scales with rank and king distance
        // Precompute king squares
        Square wking = board.kingSq(Color::WHITE);
        Square bking = board.kingSq(Color::BLACK);

        // White passed pawns
        Bitboard wp = white_pawns;
        while (wp.getBits()) {
            Square sq = pop_lsb(wp);
            if (sq == Square::NO_SQ) break;
            int f = static_cast<int>(sq.file());
            int r = static_cast<int>(sq.rank());

            // mask of opponent pawns on same and adjacent files ahead of this pawn
            Bitboard opp = black_pawns;
            Bitboard file_mask = Bitboard(0x0101010101010101ULL << f);
            Bitboard adjacent_files = Bitboard(0);
            if (f > 0) adjacent_files |= Bitboard(0x0101010101010101ULL << (f - 1));
            if (f < 7) adjacent_files |= Bitboard(0x0101010101010101ULL << (f + 1));
            // squares ahead of pawn (r+1 .. 7)
            uint64_t ahead_mask = 0ULL;
            for (int rr = r + 1; rr < 8; ++rr) ahead_mask |= (0xFFULL << (rr*8));
            Bitboard blocking = opp & (file_mask | adjacent_files) & Bitboard(ahead_mask);
            if (!blocking.getBits()) {
                // base bonus increases with rank
                int base = 25 + r * 20;
                // bonus if king is far from promotion square
                int promotion_sq_idx = (7 * 8 + f);
                int king_idx = wking.index();
                int king_dist = std::abs((promotion_sq_idx / 8) - (king_idx / 8)) + std::abs((promotion_sq_idx % 8) - (king_idx % 8));
                int king_penalty = std::max(0, 10 - king_dist) * 5; // if king near, reduce bonus
                score += base + (r * 3) + king_penalty;
            }
        }

        // Black passed pawns
        Bitboard bp = black_pawns;
        while (bp.getBits()) {
            Square sq = pop_lsb(bp);
            if (sq == Square::NO_SQ) break;
            int f = static_cast<int>(sq.file());
            int r = static_cast<int>(sq.rank()); // 0..7
            // for black, advancement measured from rank 7 down
            int adv = 7 - r;

            Bitboard opp = white_pawns;
            Bitboard file_mask = Bitboard(0x0101010101010101ULL << f);
            Bitboard adjacent_files = Bitboard(0);
            if (f > 0) adjacent_files |= Bitboard(0x0101010101010101ULL << (f - 1));
            if (f < 7) adjacent_files |= Bitboard(0x0101010101010101ULL << (f + 1));
            // squares ahead of pawn for black (0 .. r-1)
            uint64_t ahead_mask = 0ULL;
            for (int rr = 0; rr < r; ++rr) ahead_mask |= (0xFFULL << (rr*8));
            Bitboard blocking = opp & (file_mask | adjacent_files) & Bitboard(ahead_mask);
            if (!blocking.getBits()) {
                int base = 25 + adv * 20;
                int promotion_sq_idx = (0 * 8 + f);
                int king_idx = bking.index();
                int king_dist = std::abs((promotion_sq_idx / 8) - (king_idx / 8)) + std::abs((promotion_sq_idx % 8) - (king_idx % 8));
                int king_penalty = std::max(0, 10 - king_dist) * 5;
                score -= (base + (adv * 3) + king_penalty);
            }
        }

        return score;
    }

    
    int evaluateMobility(const Board& board) {
        int score = 0;
        
        // Simple mobility evaluation
        Board temp_board = board;
        Movelist white_moves, black_moves;
        
        temp_board.setFen(board.getFen());
        // Generate moves for both sides from the same base position
        movegen::legalmoves(white_moves, temp_board);
        temp_board.makeNullMove();
        movegen::legalmoves(black_moves, temp_board);
        temp_board.unmakeMove(Move::NULL_MOVE);
        
        int game_phase = getGamePhase(board);
        bool opening_phase = (game_phase >= 20);
        
        auto effectiveMobility = [&](const Movelist& moves, Color side) {
            int count = 0;
            for (const Move& m : moves) {
                Piece p = board.at(m.from());
                if (p == Piece::NONE) continue;
                // In the opening, discount queen mobility to avoid early queen sorties
                if (opening_phase && p.type() == PieceType::QUEEN) continue;
                count++;
            }
            return count;
        };
        
        int white_mob = effectiveMobility(white_moves, Color::WHITE);
        int black_mob = effectiveMobility(black_moves, Color::BLACK);
        int diff = white_mob - black_mob;
        
        // Scale mobility more in later phases
        int weight = (game_phase >= 20) ? 1 : (game_phase >= 12 ? 2 : 3);
        score += diff * weight;
        
        return score;
    }
    
    int evaluateKingSafety(const Board& board) {
        int score = 0;
        
        Square white_king = board.kingSq(Color::WHITE);
        Square black_king = board.kingSq(Color::BLACK);
        
        // Penalty for exposed king in middlegame
        int game_phase = getGamePhase(board);
        if (game_phase > 12) { // Still in middlegame
            // Check pawn shield
            Bitboard white_pawns = board.pieces(PieceType::PAWN, Color::WHITE);
            Bitboard black_pawns = board.pieces(PieceType::PAWN, Color::BLACK);
            
            // White king safety
            if (static_cast<int>(white_king.rank()) == 0) {
                int f = static_cast<int>(white_king.file());
                uint64_t files = 0ULL;
                if (f > 0) files |= 1ULL << (f - 1);
                files |= 1ULL << f;
                if (f < 7) files |= 1ULL << (f + 1);
                uint64_t shield_bits = (files << 8); // rank 2
                int shield_pawns = popcount(white_pawns & Bitboard(shield_bits));
                score += shield_pawns * 10;
            }
            
            // Black king safety
            if (static_cast<int>(black_king.rank()) == 7) {
                int f = static_cast<int>(black_king.file());
                uint64_t files = 0ULL;
                if (f > 0) files |= 1ULL << (f - 1);
                files |= 1ULL << f;
                if (f < 7) files |= 1ULL << (f + 1);
                uint64_t shield_bits = (files << 48); // rank 7
                int shield_pawns = popcount(black_pawns & Bitboard(shield_bits));
                score -= shield_pawns * 10;
            }
        }
        
        return score;
    }
    
    int evaluate(const Board& board) {
        // Check evaluation cache
        uint64_t hash = board.hash();
        int cache_index = static_cast<int>(hash % EVAL_CACHE_SIZE);
        if (eval_cache[cache_index].hash == hash) {
            return eval_cache[cache_index].score;
        }
        
        // Check for game over
        auto gameResult = board.isGameOver();
        GameResultReason result = gameResult.first;
        
        if (result != GameResultReason::NONE) {
            if (result == GameResultReason::CHECKMATE) {
                return board.sideToMove() == Color::WHITE ? -INF : INF;
            }
            return 0; // Draw
        }
        
        // Probe Syzygy if in endgame
        // int syzygy_score = probeSyzygyMove();
        // if (syzygy_score != INT_MIN) {
        //     return syzygy_score;
        // }
        
        int score = 0;
        int game_phase = getGamePhase(board);
        
        // Material and positional evaluation
        for (int sq = 0; sq < 64; sq++) {
            Square square = Square(sq);
            Piece piece = board.at(square);
            
            if (piece == Piece::NONE) continue;
            
            PieceType pieceType = piece.type();
            Color pieceColor = piece.color();
            
            int pieceValue = PIECE_VALUES[static_cast<int>(pieceType)];
            int positionalValue = getPositionalValue(pieceType, square, pieceColor, game_phase);
            
            int totalValue = pieceValue + positionalValue;
            
            if (pieceColor == Color::WHITE) {
                score += totalValue;
            } else {
                score -= totalValue;
            }
        }
        
        // Advanced evaluation features
        score += evaluatePawnStructure(board);
        score += evaluateMobility(board);
        score += evaluateKingSafety(board);
        
        // Bishop pair bonus
        if (popcount(board.pieces(PieceType::BISHOP, Color::WHITE)) >= 2) {
            score += 30;
        }
        if (popcount(board.pieces(PieceType::BISHOP, Color::BLACK)) >= 2) {
            score -= 30;
        }
        
        // Tempo bonus for side to move
        score += (board.sideToMove() == Color::WHITE) ? 10 : -10;
        

        // Determine endgame and apply endgame-specific heuristics
        bool endgame = isEndgamePosition(board);

        if (endgame) {
            // King centralization / activity bonus in endgame
            Square wking = board.kingSq(Color::WHITE);
            Square bking = board.kingSq(Color::BLACK);
            auto central_dist = [&](Square s) {
                if (s == Square::NO_SQ) return 10;
                int f = static_cast<int>(s.file());
                int r = static_cast<int>(s.rank());
                // center is around d4/e4/d5/e5 -> coords 3/4,3/4
                int df = std::abs(f - 3) + std::abs(f - 4);
                int dr = std::abs(r - 3) + std::abs(r - 4);
                // rough centrality score: smaller is better -> convert to bonus
                int dist = std::min({std::abs(f - 3) + std::abs(r - 3),
                                    std::abs(f - 3) + std::abs(r - 4),
                                    std::abs(f - 4) + std::abs(r - 3),
                                    std::abs(f - 4) + std::abs(r - 4)});
                return dist;
            };
            int wc = central_dist(wking);
            int bc = central_dist(bking);
            score += (6 - wc) * 20; // reward white king being centralized
            score -= (6 - bc) * 20; // penalize black king centralization advantage

            // Rook seventh-rank and open/semi-open file bonuses
            Bitboard wrooks = board.pieces(PieceType::ROOK, Color::WHITE);
            Bitboard brooks = board.pieces(PieceType::ROOK, Color::BLACK);

            auto file_has_pawn = [&](int file, Color c) {
                Bitboard pawns = board.pieces(PieceType::PAWN, c);
                return ((pawns.getBits() >> (file)) & 0x0101010101010101ULL) != 0ULL;
            };

            uint64_t wrbits = wrooks.getBits();
            while (wrbits) {
                int idx = __builtin_ctzll(wrbits);
                wrbits &= (wrbits - 1);
                int r = idx / 8;
                int f = idx % 8;
                // white rook on 7th (rank 6)
                if (r == 6) {
                    // less bonus if opponent has pawn on that file
                    int bonus = file_has_pawn(f, Color::BLACK) ? 30 : 70;
                    score += bonus;
                }
                // semi-open/open file bonus
                if (!file_has_pawn(f, Color::WHITE)) {
                    int bonus = file_has_pawn(f, Color::BLACK) ? 25 : 45;
                    score += bonus;
                }
            }
            uint64_t brbits = brooks.getBits();
            while (brbits) {
                int idx = __builtin_ctzll(brbits);
                brbits &= (brbits - 1);
                int r = idx / 8;
                int f = idx % 8;
                if (r == 1) { // black rook on white's 7th-rank (rank=1)
                    int bonus = file_has_pawn(f, Color::WHITE) ? 30 : 70;
                    score -= bonus;
                }
                if (!file_has_pawn(f, Color::BLACK)) {
                    int bonus = file_has_pawn(f, Color::WHITE) ? 25 : 45;
                    score -= bonus;
                }
            }
        }


        // Check penalty
        if (board.inCheck()) {
            score += (board.sideToMove() == Color::WHITE) ? -50 : 50;
        }
        
        // Early queen penalty: discourage queen development before minor pieces in the opening
        if (game_phase >= 18) {
            auto isMinorStartSquare = [&](Color c, PieceType pt, Square s) {
                if (pt == PieceType::KNIGHT) {
                    if (c == Color::WHITE) {
                        return (static_cast<int>(s.rank()) == 0 && (static_cast<int>(s.file()) == 1 || static_cast<int>(s.file()) == 6));
                    } else {
                        return (static_cast<int>(s.rank()) == 7 && (static_cast<int>(s.file()) == 1 || static_cast<int>(s.file()) == 6));
                    }
                }
                if (pt == PieceType::BISHOP) {
                    if (c == Color::WHITE) {
                        return (static_cast<int>(s.rank()) == 0 && (static_cast<int>(s.file()) == 2 || static_cast<int>(s.file()) == 5));
                    } else {
                        return (static_cast<int>(s.rank()) == 7 && (static_cast<int>(s.file()) == 2 || static_cast<int>(s.file()) == 5));
                    }
                }
                return false;
            };
            int minorsDevelopedWhite = 0, minorsDevelopedBlack = 0;
            for (int sqi = 0; sqi < 64; ++sqi) {
                Square s = Square(sqi);
                Piece p = board.at(s);
                if (p == Piece::NONE) continue;
                PieceType pt = p.type();
                if (pt == PieceType::KNIGHT || pt == PieceType::BISHOP) {
                    if (!isMinorStartSquare(p.color(), pt, s)) {
                        if (p.color() == Color::WHITE) ++minorsDevelopedWhite; else ++minorsDevelopedBlack;
                    }
                }
            }
            auto queenSquare = [&](Color c) -> Square {
                Bitboard qb = board.pieces(PieceType::QUEEN, c);
                if (!qb.getBits()) return Square::NO_SQ;
                int idx = __builtin_ctzll(qb.getBits());
                return Square(idx);
            };
            Square wq = queenSquare(Color::WHITE);
            Square bq = queenSquare(Color::BLACK);
            auto isQueenOnHome = [&](Color c, Square qsq) {
                if (qsq == Square::NO_SQ) return true; // no queen, ignore
                int r = static_cast<int>(qsq.rank());
                int f = static_cast<int>(qsq.file());
                return (c == Color::WHITE) ? (r == 0 && f == 3) : (r == 7 && f == 3);
            };
            if (!isQueenOnHome(Color::WHITE, wq) && minorsDevelopedWhite < 2) {
                score -= 40;
            }
            if (!isQueenOnHome(Color::BLACK, bq) && minorsDevelopedBlack < 2) {
                score += 40;
            }
        }

        // Opening principles heuristics to avoid odd knight shuffling and encourage development
        if (game_phase >= 18) {
            // Center pawn bonuses (encourage e4/d4; discourage opponent e5/d5)
            auto hasPawnOn = [&](Color c, int file, int rank) {
                Bitboard pawns = board.pieces(PieceType::PAWN, c);
                int idx = rank * 8 + file;
                return ((pawns.getBits() >> idx) & 1ULL) != 0ULL;
            };
            if (hasPawnOn(Color::WHITE, 4, 3)) score += 15; // e4
            if (hasPawnOn(Color::WHITE, 3, 3)) score += 15; // d4
            if (hasPawnOn(Color::BLACK, 4, 4)) score -= 15; // e5
            if (hasPawnOn(Color::BLACK, 3, 4)) score -= 15; // d5
            // Light bonus for c4/f4 (space/gambits ok but smaller)
            if (hasPawnOn(Color::WHITE, 2, 3)) score += 5;  // c4
            if (hasPawnOn(Color::WHITE, 5, 3)) score += 5;  // f4
            if (hasPawnOn(Color::BLACK, 2, 4)) score -= 5;  // c5
            if (hasPawnOn(Color::BLACK, 5, 4)) score -= 5;  // f5

            // Knight rim penalties and good squares bonuses
            auto applyKnightHeuristics = [&](Color c) {
                Bitboard knights = board.pieces(PieceType::KNIGHT, c);
                uint64_t bits = knights.getBits();
                while (bits) {
                    int idx = __builtin_ctzll(bits);
                    bits &= (bits - 1);
                    int f = idx % 8;
                    int r = idx / 8;
                    // Rim penalty (Na/h or rank 1/8)
                    if (f == 0 || f == 7) {
                        score += (c == Color::WHITE ? -12 : 12);
                    }
                    // Good development squares
                    if (c == Color::WHITE) {
                        if ((f == 2 && r == 2) || (f == 5 && r == 2)) score += 12; // c3, f3
                    } else {
                        if ((f == 2 && r == 5) || (f == 5 && r == 5)) score -= 12; // c6, f6 (bad for white)
                    }
                }
            };
            applyKnightHeuristics(Color::WHITE);
            applyKnightHeuristics(Color::BLACK);

            // Bishop development: bonus for leaving back rank; extra for aiming at center
            auto applyBishopHeuristics = [&](Color c) {
                Bitboard bishops = board.pieces(PieceType::BISHOP, c);
                uint64_t bits = bishops.getBits();
                while (bits) {
                    int idx = __builtin_ctzll(bits);
                    bits &= (bits - 1);
                    int f = idx % 8;
                    int r = idx / 8;
                    if (c == Color::WHITE) {
                        if (r > 0) score += 8; // off back rank
                        // Squares like c4, b5, g5, e2 get a small extra
                        if ((f == 2 && r == 3) || (f == 1 && r == 4) || (f == 6 && r == 4) || (f == 4 && r == 1)) score += 6;
                    } else {
                        if (r < 7) score -= 8;
                        if ((f == 2 && r == 4) || (f == 1 && r == 3) || (f == 6 && r == 3) || (f == 4 && r == 6)) score -= 6;
                    }
                }
            };
            applyBishopHeuristics(Color::WHITE);
            applyBishopHeuristics(Color::BLACK);

            // Castling incentive: king on g1/c1 (or g8/c8) in opening gets a bonus
            auto kingSqW = board.kingSq(Color::WHITE);
            auto kingSqB = board.kingSq(Color::BLACK);
            if ((static_cast<int>(kingSqW.file()) == 6 && static_cast<int>(kingSqW.rank()) == 0) ||
                (static_cast<int>(kingSqW.file()) == 2 && static_cast<int>(kingSqW.rank()) == 0)) {
                score += 20;
            }
            if ((static_cast<int>(kingSqB.file()) == 6 && static_cast<int>(kingSqB.rank()) == 7) ||
                (static_cast<int>(kingSqB.file()) == 2 && static_cast<int>(kingSqB.rank()) == 7)) {
                score -= 20;
            }
        }
        
        // Store in cache
        eval_cache[cache_index] = {hash, score};
        
        return score;
    }
    
    int mvvLvaScore(const Move& move, const Board& board) {
        Piece victim = board.at(move.to());
        Piece attacker = board.at(move.from());
        
        if (victim == Piece::NONE) return 0;
        if (attacker == Piece::NONE) {
            return PIECE_VALUES[static_cast<int>(victim.type())] * 10;
        }
        
        // MVV-LVA: Most Valuable Victim - Least Valuable Attacker
        return PIECE_VALUES[static_cast<int>(victim.type())] * 10 - 
               PIECE_VALUES[static_cast<int>(attacker.type())];
    }
    
    void orderMoves(Movelist& moves, const Board& board, int depth, Move tt_move = Move::NULL_MOVE) {
        if (moves.empty()) return;
        
        std::vector<std::pair<int, Move>> move_scores;
        move_scores.reserve(moves.size());
        
        for (const Move& move : moves) {
            int score = 0;
            
            // 1. Hash move (best move from transposition table)
            if (move == tt_move) {
                score = 10000000;
            }
            // 2. Winning captures (SEE > 0)
            else if (board.at(move.to()) != Piece::NONE) {
                int see_value = mvvLvaScore(move, board);
                if (see_value > 0) {
                    score = 1000000 + see_value;
                } else {
                    score = -100000 + see_value; // Losing captures ordered last
                }
            }
            // 3. Killer moves
            else if (depth >= 0 && move == killer_moves[depth][0]) {
                score = 900000;
            }
            else if (depth >= 0 && move == killer_moves[depth][1]) {
                score = 800000;
            }
            // 4. Counter moves
            else if (depth > 0 && lastMoveOnBoard() != Move::NULL_MOVE) {
                Move last = lastMoveOnBoard();
                int lf = last.from().index();
                int lt = last.to().index();
                if (lf >= 0 && lt >= 0 && lf < 64 && lt < 64) {
                    if (move == counter_moves[lf][lt]) {
                        score = 700000;
                    }
                }
            }
            // 5. History heuristic
            else {
                int f = move.from().index();
                int t = move.to().index();
                if (f >= 0 && t >= 0 && f < 64 && t < 64)
                    score = history_table[f][t];
                else
                    score = 0;
            }
            
            // Add small random noise to prevent repetitive play
            score += (rng() % 10);
            
            move_scores.emplace_back(score, move);
        }
        
        // Sort moves by score
        std::sort(move_scores.begin(), move_scores.end(), 
                  [](const auto& a, const auto& b) { return a.first > b.first; });
        
        // Copy sorted moves back
        for (size_t i = 0; i < moves.size(); i++) {
            moves[i] = move_scores[i].second;
        }
    }
    
    void updatePV(Move move, int ply) {
        if (ply < 0 || ply >= 63) return;
        pv_table.pv[ply][0] = move;
        for (int i = 0; i < pv_table.pv_length[ply + 1] && i < 63; i++) {
            pv_table.pv[ply][i + 1] = pv_table.pv[ply + 1][i];
        }
        pv_table.pv_length[ply] = std::min(63, pv_table.pv_length[ply + 1] + 1);
    }
    
    void storeTT(uint64_t hash, int score, int depth, TTEntry::Flag flag, Move best_move) {
        int index = static_cast<int>(hash % static_cast<uint64_t>(tt_size));
        TTEntry& entry = transposition_table[index];
        
        // Replacement strategy: always replace if deeper or same position
        if (entry.hash == 0 || entry.hash == hash || 
            depth >= entry.depth || entry.age < tt_age - 2) {
            entry.hash = hash;
            entry.score = score;
            entry.depth = depth;
            entry.flag = flag;
            entry.best_move = best_move;
            entry.age = tt_age;
        }
    }
    
    bool probeTT(uint64_t hash, int& score, int depth, int alpha, int beta, Move& best_move) {
        int index = static_cast<int>(hash % static_cast<uint64_t>(tt_size));
        const TTEntry& entry = transposition_table[index];
        
        if (entry.hash == hash) {
            tt_hits++;
            best_move = entry.best_move;
            
            if (entry.depth >= depth) {
                if (entry.flag == TTEntry::EXACT) {
                    score = entry.score;
                    return true;
                }
                else if (entry.flag == TTEntry::LOWER_BOUND && entry.score >= beta) {
                    score = beta;
                    return true;
                }
                else if (entry.flag == TTEntry::UPPER_BOUND && entry.score <= alpha) {
                    score = alpha;
                    return true;
                }
            }
        }
        
        return false;
    }
    
    int quiescence(Board& board, int alpha, int beta, int depth = 0) {
        nodes_searched.fetch_add(1);
        
        if (stop_search.load() || depth > 10) {
            return evaluate(board);
        }
        
        int stand_pat = evaluate(board);
        
        if (stand_pat >= beta) {
            return beta;
        }
        
        if (alpha < stand_pat) {
            alpha = stand_pat;
        }
        
        Movelist moves;
        movegen::legalmoves<movegen::MoveGenType::CAPTURE>(moves, board);
        orderMoves(moves, board, 0);
        
        for (const Move& move : moves) {
            // Delta pruning
            Piece captured = board.at(move.to());
            if (captured != Piece::NONE) {
                int delta = stand_pat + PIECE_VALUES[static_cast<int>(captured.type())] + 200;
                if (delta < alpha) {
                    continue;
                }
            }
            
            makeMoveOnBoard(move);
            int score = -quiescence(board, -beta, -alpha, depth + 1);
            unmakeMoveOnBoard(move);
            
            if (score >= beta) {
                return beta;
            }
            
            if (score > alpha) {
                alpha = score;
            }
        }
        
        return alpha;
    }
    
    // int alphaBeta(Board& board, int depth, int alpha, int beta, bool maximizing, 
    //               std::chrono::steady_clock::time_point start_time, int time_limit, 
    //               int ply = 0, bool do_null = true) {
        
    //     nodes_searched.fetch_add(1);
    //     if (ply >= 0 && ply < 64) pv_table.pv_length[ply] = 0;
        
    //     if (stop_search.load()) {
    //         return evaluate(board);
    //     }
        
    //     // Check time
    //     if ((nodes_searched.load() & 2047) == 0) { // Check every 2048 nodes
    //         auto current_time = std::chrono::steady_clock::now();
    //         auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
    //         if (elapsed.count() > time_limit) {
    //             stop_search.store(true);
    //             return evaluate(board);
    //         }
    //     }
        
    //     // Check for game over
    //     auto gameResult = board.isGameOver();
    //     if (gameResult.first != GameResultReason::NONE) {
    //         if (gameResult.first == GameResultReason::CHECKMATE) {
    //             return maximizing ? -INF + ply : INF - ply;
    //         }
    //         return 0; // Draw
    //     }
        
    //     // Mate distance pruning
    //     int mate_value = INF - ply;
    //     if (alpha >= mate_value) return mate_value;
    //     if (beta <= -mate_value) return -mate_value;
    //     alpha = std::max(alpha, -mate_value);
    //     beta = std::min(beta, mate_value);
        
    //     if (depth <= 0) {
    //         return quiescence(board, alpha, beta);
    //     }
        
    //     // Transposition table probe
    //     uint64_t hash = board.hash();
    //     Move tt_move = Move::NULL_MOVE;
    //     int tt_score = 0;
        
    //     if (probeTT(hash, tt_score, depth, alpha, beta, tt_move)) {
    //         return tt_score;
    //     }
        
    //     // Null move pruning
    //     if (do_null && depth >= 3 && !board.inCheck() && beta > -INF + 100) {
    //         int material = 0;
    //         for (int sq = 0; sq < 64; sq++) {
    //             Piece p = board.at(Square(sq));
    //             if (p != Piece::NONE && p.color() == board.sideToMove()) {
    //                 material += PIECE_VALUES[static_cast<int>(p.type())];
    //             }
    //         }
            
    //         if (material > 500) { // Don't null move in endgame
    //             makeNullMoveOnBoard();
    //             int R = 2 + (depth >= 6 ? 1 : 0); // Adaptive null move reduction
    //             int score = -alphaBeta(board, depth - R - 1, -beta, -beta + 1, !maximizing, 
    //                                   start_time, time_limit, ply + 1, false);
    //             unmakeNullMoveOnBoard();
                
    //             if (score >= beta) {
    //                 return beta;
    //             }
    //         }
    //     }
        
    //     // Internal iterative deepening
    //     if (depth >= 6 && tt_move == Move::NULL_MOVE) {
    //         alphaBeta(board, depth - 2, alpha, beta, maximizing, start_time, time_limit, ply, false);
    //         probeTT(hash, tt_score, depth - 2, alpha, beta, tt_move);
    //     }
        
    //     // Generate and order moves
    //     Movelist moves;
    //     movegen::legalmoves(moves, board);
    //     orderMoves(moves, board, ply, tt_move);
        
    //     if (moves.empty()) {
    //         if (board.inCheck()) {
    //             return maximizing ? -INF + ply : INF - ply;
    //         }
    //         return 0; // Stalemate
    //     }
        
    //     int bestValue = maximizing ? NEG_INF : INF;
    //     Move bestMove = moves[0];
    //     TTEntry::Flag flag = TTEntry::UPPER_BOUND;
    //     int moves_searched = 0;
        
    //     for (const Move& move : moves) {
    //         if (stop_search.load()) break;
            
    //         makeMoveOnBoard(move);
    //         int value;
            
    //         // Late move reduction (LMR)
    //         if (moves_searched >= 4 && depth >= 3 && !board.inCheck() && 
    //             board.at(move.to()) == Piece::NONE && 
    //             move != killer_moves[ply][0] && move != killer_moves[ply][1]) {
                
    //             int reduction = 1;
    //             if (moves_searched >= 8) reduction = 2;
                
    //             // Reduced depth search
    //             value = -alphaBeta(board, depth - reduction - 1, -alpha - 1, -alpha, !maximizing,
    //                              start_time, time_limit, ply + 1, true);
                
    //             // Re-search if it beats alpha
    //             if (value > alpha && value < beta) {
    //                 value = -alphaBeta(board, depth - 1, -beta, -alpha, !maximizing,
    //                                  start_time, time_limit, ply + 1, true);
    //             }
    //         }
    //         // Principal variation search (PVS)
    //         else if (moves_searched > 0) {
    //             value = -alphaBeta(board, depth - 1, -alpha - 1, -alpha, !maximizing,
    //                              start_time, time_limit, ply + 1, true);
    //             if (value > alpha && value < beta) {
    //                 value = -alphaBeta(board, depth - 1, -beta, -alpha, !maximizing,
    //                                  start_time, time_limit, ply + 1, true);
    //             }
    //         }
    //         else {
    //             value = -alphaBeta(board, depth - 1, -beta, -alpha, !maximizing,
    //                              start_time, time_limit, ply + 1, true);
    //         }
            
    //         unmakeMoveOnBoard(move);
    //         moves_searched++;
            
    //         if (maximizing) {
    //             if (value > bestValue) {
    //                 bestValue = value;
    //                 bestMove = move;
                    
    //                 if (value > alpha) {
    //                     alpha = value;
    //                     flag = TTEntry::EXACT;
    //                     updatePV(move, ply);
    //                 }
    //             }
    //         } else {
    //             if (value < bestValue) {
    //                 bestValue = value;
    //                 bestMove = move;
                    
    //                 if (value < beta) {
    //                     beta = value;
    //                     flag = TTEntry::EXACT;
    //                     updatePV(move, ply);
    //                 }
    //             }
    //         }
            
    //         if (beta <= alpha) {
    //             flag = TTEntry::LOWER_BOUND;
                
    //             // Update killer moves and history
    //             if (board.at(move.to()) == Piece::NONE) {
    //                 if (ply >= 0 && ply < 64) {
    //                     if (killer_moves[ply][0] != move) {
    //                         killer_moves[ply][1] = killer_moves[ply][0];
    //                         killer_moves[ply][0] = move;
    //                     }
    //                 }
                    
    //                 int f = move.from().index();
    //                 int t = move.to().index();
    //                 if (f >= 0 && t >= 0 && f < 64 && t < 64) {
    //                     history_table[f][t] += depth * depth;
    //                     if (history_table[f][t] > 100000) {
    //                         // Age history table
    //                         for (int i = 0; i < 64; i++) {
    //                             for (int j = 0; j < 64; j++) {
    //                                 history_table[i][j] /= 2;
    //                             }
    //                         }
    //                     }
    //                 }
                    
    //                 // Update counter move
    //                 if (ply > 0 && lastMoveOnBoard() != Move::NULL_MOVE) {
    //                     Move last = lastMoveOnBoard();
    //                     int lf = last.from().index();
    //                     int lt = last.to().index();
    //                     if (lf >= 0 && lt >= 0 && lf < 64 && lt < 64) {
    //                         counter_moves[lf][lt] = move;
    //                     }
    //                 }
    //             }
    //             break;
    //         }
    //     }
        
    //     if (!stop_search.load()) {
    //         storeTT(hash, bestValue, depth, flag, bestMove);
    //     }
        
    //     return bestValue;
    // }

    // int alphaBeta(Board& board, int depth, int alpha, int beta, bool maximizing,
    //           std::chrono::steady_clock::time_point start_time, int time_limit,
    //           int ply = 0, bool do_null = true) {
    //     nodes_searched.fetch_add(1);
    //     pv_table.pv_length[ply] = 0;

    //     if (stop_search.load()) return evaluate(board);

    //     auto hard_deadline = start_time + std::chrono::milliseconds(time_limit);

    //     // Check time more frequently
    //     if ((nodes_searched.load() & 511) == 0) { // every 512 nodes
    //         if (std::chrono::steady_clock::now() >= hard_deadline) {
    //             stop_search.store(true);
    //             return evaluate(board);
    //         }
    //     }

    //     // Check game over
    //     auto gameResult = board.isGameOver();
    //     if (gameResult.first != GameResultReason::NONE) {
    //         if (gameResult.first == GameResultReason::CHECKMATE) {
    //             return maximizing ? -30000 + ply : 30000 - ply;
    //         }
    //         return 0; // Draw
    //     }

    //     // Mate distance pruning
    //     int mate_value = 30000 - ply;
    //     if (alpha >= mate_value) return mate_value;
    //     if (beta <= -mate_value) return -mate_value;
    //     alpha = std::max(alpha, -mate_value);
    //     beta = std::min(beta, mate_value);

    //     if (depth <= 0) return quiescence(board, alpha, beta);

    //     // Transposition table probe
    //     uint64_t hash = board.hash();
    //     Move tt_move = Move::NULL_MOVE;
    //     int tt_score;
    //     if (probeTT(hash, tt_score, depth, alpha, beta, tt_move)) {
    //         return tt_score;
    //     }

    //     // Move generation
    //     Movelist moves;
    //     movegen::legalmoves(moves, board);
    //     orderMoves(moves, board, ply, tt_move);

    //     if (moves.empty()) {
    //         if (board.inCheck()) return maximizing ? -30000 + ply : 30000 - ply;
    //         return 0; // Stalemate
    //     }

    //     int bestValue = maximizing ? INT_MIN : INT_MAX;
    //     Move bestMove = moves[0];
    //     TTEntry::Flag flag = TTEntry::UPPER_BOUND;

    //     for (const Move& move : moves) {
    //         if (stop_search.load()) break;

    //         makeMoveOnBoard(move);
    //         int value = -alphaBeta(board, depth - 1, -beta, -alpha, !maximizing,
    //                             start_time, time_limit, ply + 1, true);
    //         unmakeMoveOnBoard(move);

    //         if (maximizing) {
    //             if (value > bestValue) {
    //                 bestValue = value;
    //                 bestMove = move;
    //                 if (value > alpha) {
    //                     alpha = value;
    //                     flag = TTEntry::EXACT;
    //                     updatePV(move, ply);
    //                 }
    //             }
    //         } else {
    //             if (value < bestValue) {
    //                 bestValue = value;
    //                 bestMove = move;
    //                 if (value < beta) {
    //                     beta = value;
    //                     flag = TTEntry::EXACT;
    //                     updatePV(move, ply);
    //                 }
    //             }
    //         }

    //         if (beta <= alpha) {
    //             flag = TTEntry::LOWER_BOUND;
    //             break;
    //         }
    //     }

    //     if (!stop_search.load()) {
    //         storeTT(hash, bestValue, depth, flag, bestMove);
    //     }

    //     return bestValue;
    // }

    // Replace the existing alphaBeta(...) with this negamax-style implementation.
// Note: signature drops the 'maximizing' bool.
    int alphaBeta(Board& board, int depth, int alpha, int beta,
              std::chrono::steady_clock::time_point start_time, int time_limit,
              int ply = 0, bool do_null = true) {
        nodes_searched.fetch_add(1);
        pv_table.pv_length[ply] = 0;

        if (stop_search.load()) return evaluate(board);

        auto hard_deadline = start_time + std::chrono::milliseconds(time_limit);

        // Check time periodically
        if ((nodes_searched.load() & 511) == 0) {
            if (std::chrono::steady_clock::now() >= hard_deadline) {
                stop_search.store(true);
                return evaluate(board);
            }
        }

        // Terminal node handling
        auto gameResult = board.isGameOver();
        if (gameResult.first != GameResultReason::NONE) {
            if (gameResult.first == GameResultReason::CHECKMATE) {
                // If side to move is mated, that's a very bad score for the side to move:
                return - (INF - ply);
            }
            return 0; // draw
        }

        // Mate distance windowing (avoid overflow/UB)
        int mate_value = INF - ply;
        if (alpha >= mate_value) return alpha;
        if (beta <= -mate_value) return beta;
        alpha = std::max(alpha, -mate_value);
        beta  = std::min(beta, mate_value);

        if (depth <= 0) {
            return quiescence(board, alpha, beta);
        }

        // Transposition table probe (returns true if exact or bound satisfied)
        uint64_t hash = board.hash();
        Move tt_move = Move::NULL_MOVE;
        int tt_score = 0;
        if (probeTT(hash, tt_score, depth, alpha, beta, tt_move)) {
            return tt_score;
        }

        // Move generation and ordering
        Movelist moves;
        movegen::legalmoves(moves, board);
        orderMoves(moves, board, ply, tt_move);

        if (moves.empty()) {
            // no legal moves -> mate or stalemate already handled earlier, but double-check
            if (board.inCheck()) return - (INF - ply);
            return 0;
        }

        int bestValue = -INF;
        Move bestMove = Move::NULL_MOVE;
        TTEntry::Flag flag = TTEntry::UPPER_BOUND;

        bool first = true;
        for (const Move& m : moves) {
            if (stop_search.load()) break;

            makeMoveOnBoard(m);

            int score;
            // Principal variation search: full window for first move, narrow window for others
            if (first) {
                score = -alphaBeta(board, depth - 1, -beta, -alpha, start_time, time_limit, ply + 1, do_null);
                first = false;
            } else {
                // search with a null-window for speed (PVS)
                score = -alphaBeta(board, depth - 1, -alpha - 1, -alpha, start_time, time_limit, ply + 1, do_null);
                if (score > alpha && score < beta) {
                    // Re-search with full window if null-window suggests it might be better
                    score = -alphaBeta(board, depth - 1, -beta, -alpha, start_time, time_limit, ply + 1, do_null);
                }
            }

            unmakeMoveOnBoard(m);

            if (stop_search.load()) break;

            if (score > bestValue) {
                bestValue = score;
                bestMove = m;
                // update PV
                pv_table.pv[ply][0] = m;
                for (int i = 0; i < pv_table.pv_length[ply + 1] && i < 63; ++i)
                    pv_table.pv[ply][i + 1] = pv_table.pv[ply + 1][i];
                pv_table.pv_length[ply] = std::min(63, pv_table.pv_length[ply + 1] + 1);
            }

            if (bestValue > alpha) {
                alpha = bestValue;
            }

            if (alpha >= beta) {
                // Beta cutoff
                flag = TTEntry::LOWER_BOUND;
                // update killer/history heuristics for quiet moves
                if (board.at(m.to()) == Piece::NONE) {
                    if (killer_moves[ply][0] != m) {
                        killer_moves[ply][1] = killer_moves[ply][0];
                        killer_moves[ply][0] = m;
                    }
                    int f = m.from().index(), t = m.to().index();
                    if (f >= 0 && t >= 0 && f < 64 && t < 64)
                        history_table[f][t] += depth * depth;
                }
                break;
            }
        }

        if (!stop_search.load()) {
            // store TT with correct flag (if no cutoff we may have exact)
            if (bestValue <= alpha) {
                // already set by comparisons; keep flag
            }
            // Determine exactness properly: if not a cutoff and not upper bound set exact
            if (flag != TTEntry::LOWER_BOUND) {
                flag = (bestValue <= alpha) ? TTEntry::UPPER_BOUND : TTEntry::EXACT;
            }
            storeTT(hash, bestValue, depth, flag, bestMove);
        }

        return bestValue;
    }


    
    // Move findBestMove(int max_depth, int time_limit) {

    //     // --- Syzygy check ---
    //     int tbScore;
    //     Move tbMove = probeSyzygyMove(tbScore);
    //     if (tbMove != Move::NULL_MOVE) {
    //         std::cout << "info string Using Syzygy tablebases" << std::endl;
    //         std::cout << "info depth 0 score cp " << tbScore << " pv " 
    //                 << uci::moveToUci(tbMove) << std::endl;
    //         return tbMove; // Perfect move from tablebase
    //     }

    //     // Check opening book first
    //     Move book_move = getBookMove();
    //     if (book_move != Move::NULL_MOVE) {
    //         std::cout << "info string Using opening book" << std::endl;
    //         return book_move;
    //     }
        
    //     stop_search.store(false);
    //     tt_age++;
    //     nodes_searched.store(0);
    //     tt_hits = 0;
    //     pv_table.clear();
        
    //     auto start_time = std::chrono::steady_clock::now();
        
    //     Movelist moves;
    //     movegen::legalmoves(moves, board);
        
    //     if (moves.empty()) {
    //         return Move::NULL_MOVE;
    //     }
        
    //     if (moves.size() == 1) {
    //         return moves[0]; // Only one legal move
    //     }
        
    //     Move bestMove = moves[0];
    //     int bestValue = board.sideToMove() == Color::WHITE ? NEG_INF : INF;
    //     bool maximizing = board.sideToMove() == Color::WHITE;
        
    //     // Iterative deepening
    //     for (int d = 1; d <= max_depth && !stop_search.load(); d++) {
    //         auto current_time = std::chrono::steady_clock::now();
    //         auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
            
    //         // Time management
    //         if (d > 1 && elapsed.count() > time_limit / 3) {
    //             break;
    //         }
            
    //         int currentBestValue = maximizing ? NEG_INF : INF;
    //         Move currentBestMove = bestMove;
    //         bool depth_completed = true;
            
    //         // Aspiration windows (safe, avoid overflowing NEG_INF)
    //         int window = 25;
    //         int alpha, beta;
    //         if (bestValue <= NEG_INF / 2) {
    //             alpha = NEG_INF;
    //             beta  = INF;
    //         } else if (bestValue >= INF / 2) {
    //             alpha = NEG_INF;
    //             beta  = INF;
    //         } else {
    //             alpha = std::max(NEG_INF, bestValue - window);
    //             beta  = std::min(INF,      bestValue + window);
    //         }
            
    //         if (d < 4) {
    //             alpha = NEG_INF;
    //             beta  = INF;
    //         }
            
    //         while (true) {
    //             currentBestValue = alphaBeta(board, d, alpha, beta, maximizing, 
    //                                         start_time, time_limit, 0, true);
                
    //             if (stop_search.load()) {
    //                 depth_completed = false;
    //                 break;
    //             }
                
    //             // Check aspiration window failure
    //             if (currentBestValue <= alpha) {
    //                 alpha = NEG_INF;
    //                 continue;
    //             }
    //             if (currentBestValue >= beta) {
    //                 beta = INF;
    //                 continue;
    //             }
                
    //             break;
    //         }
            
    //         if (depth_completed && !stop_search.load()) {
    //             bestValue = currentBestValue;
    //             if (pv_table.pv_length[0] > 0) {
    //                 bestMove = pv_table.pv[0][0];
    //             }
                
    //             // Output UCI info
    //             auto current_time = std::chrono::steady_clock::now();
    //             auto elapsed2 = std::chrono::duration_cast<std::chrono::milliseconds>(current_time - start_time);
                
    //             uint64_t nodes = nodes_searched.load();
    //             uint64_t nps = elapsed2.count() > 0 ? (nodes * 1000) / elapsed2.count() : 0;
    //             int hashfull = (nodes > 0) ? static_cast<int>((tt_hits * 1000) / std::max(nodes, 1ULL)) : 0;
                
    //             std::cout << "info depth " << d 
    //                      << " score cp " << bestValue 
    //                      << " time " << elapsed2.count()
    //                      << " nodes " << nodes
    //                      << " nps " << nps
    //                      << " hashfull " << hashfull
    //                      << " pv";
                
    //             for (int i = 0; i < pv_table.pv_length[0]; i++) {
    //                 std::cout << " " << uci::moveToUci(pv_table.pv[0][i]);
    //             }
    //             std::cout << std::endl;
                
    //             // Check for mate
    //             if (std::abs(bestValue) > INF - 1000) {
    //                 break; // Found mate, no need to search deeper
    //             }
    //         }
    //     }
        
    //     return bestMove;
    // }
    Move findBestMove(int max_depth, int time_limit) {
    // Always use MoveTime (ignore GUI wtime/btime)
        time_limit = move_time;  

        auto start_time = std::chrono::steady_clock::now();
        auto hard_deadline = start_time + std::chrono::milliseconds(time_limit);
        auto soft_deadline = start_time + std::chrono::milliseconds(time_limit/15);

        stop_search.store(false);
        tt_age++;
        nodes_searched.store(0);
        tt_hits = 0;
        pv_table.clear();

        Movelist moves;
        movegen::legalmoves(moves, board);
        if (moves.empty()) return Move::NULL_MOVE;
        if (moves.size() == 1) return moves[0];

        // Try Syzygy probe early for exact tablebase decisions (if available)
        if (use_syzygy) {
            int tb_score = INT_MIN;
            Move tbm = probeSyzygyMove(tb_score);
            if (tbm != Move::NULL_MOVE && tb_score != INT_MIN) {
                // If TB indicates mate/draw/win we can return TB move immediately.
                // But ensure it's legal in current position (it should be).
                return tbm;
            }
        }


        Move bestMove = moves[0];
        int bestValue = board.sideToMove() == Color::WHITE ? INT_MIN : INT_MAX;
        bool maximizing = board.sideToMove() == Color::WHITE;

        // Iterative deepening
        for (int d = 2; d <= max_depth; d+=2) {
            if (stop_search.load()) break;

            auto now = std::chrono::steady_clock::now();
            if (now >= soft_deadline && d<20) break;
            if(now>= hard_deadline) break;

            int currentBestValue = alphaBeta(board, d, -INF, INF, start_time, time_limit, 0, true);

            if (stop_search.load()) break;

            bestValue = currentBestValue;
            if (pv_table.pv_length[0] > 0) {
                bestMove = pv_table.pv[0][0];
            }

            // Print UCI info
            auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(
                            std::chrono::steady_clock::now() - start_time);
            uint64_t nodes = nodes_searched.load();
            uint64_t nps = elapsed.count() > 0 ? (nodes * 1000) / elapsed.count() : 0;
            int hashfull = (tt_hits * 1000) / std::max(nodes, 1ULL);

            std::cout << "info depth " << d
                    << " score cp " << bestValue
                    << " time " << elapsed.count()
                    << " nodes " << nodes
                    << " nps " << nps
                    << " hashfull " << hashfull
                    << " pv";

            for (int i = 0; i < pv_table.pv_length[0]; i++) {
                std::cout << " " << uci::moveToUci(pv_table.pv[0][i]);
            }
            std::cout << std::endl;

            // Stop if mate found
            if (abs(bestValue) > 29000) break;

            // Stop if very little time left
            if (std::chrono::steady_clock::now() + std::chrono::milliseconds(20) >= hard_deadline)
                break;
        }

        // Fallback if no PV move
        if (bestMove == Move::NULL_MOVE && !moves.empty()) {
            bestMove = moves[0];
        }

        return bestMove;
    }

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
                std::cout << "id name Enhanced Chess Engine v2.0\n";
                std::cout << "id author Enhanced AI\n";
                std::cout << "option name Hash type spin default 64 min 1 max 1024\n";
                std::cout << "option name Depth type spin default 12 min 1 max 30\n";
                std::cout << "option name MoveTime type spin default 60000 min 100 max 300000\n";
                std::cout << "option name UseBook type check default true\n";
                std::cout << "option name BookDepth type spin default 15 min 0 max 30\n";
                std::cout << "option name SyzygyPath type string default <empty>\n";
                std::cout << "uciok\n";
            }
            else if (command == "isready") {
                std::cout << "readyok\n";
            }
            else if (command == "ucinewgame") {
                board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
                clearTables();
                move_stack.clear();
            }
            else if (command == "position") {
                std::string subcommand;
                iss >> subcommand;
                
                if (subcommand == "startpos") {
                    board.setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
                    move_stack.clear();
                    
                    std::string moves_token;
                    if (iss >> moves_token && moves_token == "moves") {
                        std::string move_str;
                        while (iss >> move_str) {
                            Move move = uci::uciToMove(board, move_str);
                            makeMoveOnBoard(move);
                        }
                    }
                }
                else if (subcommand == "fen") {
                    std::string fen;
                    std::string word;
                    
                    // Read the 6 FEN fields (we expect them)
                    for (int i = 0; i < 6 && iss >> word; i++) {
                        if (!fen.empty()) fen += " ";
                        fen += word;
                    }
                    
                    board.setFen(fen);
                    move_stack.clear();
                    
                    // If more tokens remain and they start with "moves", process them
                    if (iss >> word && word == "moves") {
                        std::string move_str;
                        while (iss >> move_str) {
                            Move move = uci::uciToMove(board, move_str);
                            makeMoveOnBoard(move);
                        }
                    }
                }
            }
            else if (command == "go") {
                int depth = search_depth;
                int movetime = move_time;
                int wtime = 0, btime = 0, winc = 0, binc = 0;
                int movestogo = 40;
                
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
                    else if (param == "movestogo") {
                        iss >> movestogo;
                    }
                    else if (param == "infinite") {
                        movetime = 86400000; // 24 hours
                    }
                }
                
                // Improved time management
                int time_limit = movetime;
                if (wtime > 0 || btime > 0) {
                    int my_time = (board.sideToMove() == Color::WHITE) ? wtime : btime;
                    int my_inc = (board.sideToMove() == Color::WHITE) ? winc : binc;
                    
                    // Allocate time based on remaining moves
                    if (movestogo > 0) {
                        time_limit = static_cast<int>((my_time / movestogo) + my_inc * 0.8);
                    } else {
                        time_limit = static_cast<int>(my_time / 20 + my_inc * 0.8);
                    }
                    
                    // Never use more than 1/3 of remaining time
                    time_limit = std::min(time_limit, my_time / 3);
                }
                
                time_limit = std::max(time_limit, 50); // Minimum 50ms
                
                Move bestMove = findBestMove(depth, time_limit);
                if (bestMove != Move::NULL_MOVE) {
                    std::cout << "bestmove " << uci::moveToUci(bestMove) << std::endl;
                } else {
                    std::cout << "bestmove 0000" << std::endl;
                }
            }
            else if (command == "stop") {
                stop_search.store(true);
            }
            else if (command == "setoption") {
                // setoption name <name> value <x>
                std::string token;
                std::string name;
                std::string value;
                // Read until "name"
                iss >> token;
                if (token == "name") {
                    // read rest up to "value"
                    std::getline(iss, name, 'v'); // read until 'v' starts "value"
                    // This is a bit hacky; simpler parser:
                    // We'll reposition stream to start after "name"
                    iss.clear();
                    iss.seekg(0);
                    // fallback: parse simpler
                    iss >> token; // setoption
                    iss >> token; // name
                    std::getline(iss, name, 'v'); // gets name and 'alue...'
                    // rudimentary alternative: read full line and find substrings
                    std::string rest;
                    std::getline(iss, rest);
                    auto value_pos = rest.find("value");
                    if (value_pos != std::string::npos) {
                        name = rest.substr(0, value_pos);
                        value = rest.substr(value_pos + 5);
                    } else {
                        // fallback: try simpler parse
                        std::istringstream iss2(rest);
                        iss2 >> token >> value;
                    }
                }
                // Simpler dedicated parsing below for known options
                iss.clear();
                iss.seekg(0);
                std::string dummy;
                iss >> dummy; // setoption
                iss >> dummy; // name
                std::string optname;
                std::string optvalue;
                // Now read name (possibly multiple words) until "value"
                while (iss >> dummy) {
                    if (dummy == "value") break;
                    if (!optname.empty()) optname += " ";
                    optname += dummy;
                }
                // read rest as value
                std::getline(iss, optvalue);
                // trim spaces
                auto trim = [](std::string &s) {
                    while (!s.empty() && std::isspace(s.front())) s.erase(s.begin());
                    while (!s.empty() && std::isspace(s.back())) s.pop_back();
                };
                trim(optname);
                trim(optvalue);
                
                if (optname == "Hash") {
                    int mb = std::stoi(optvalue);
                    tt_size = (mb * 1048576) / static_cast<int>(sizeof(TTEntry));
                    transposition_table.resize(tt_size);
                    clearTables();
                }
                else if (optname == "Depth") {
                    search_depth = std::stoi(optvalue);
                }
                else if (optname == "MoveTime") {
                    move_time = std::stoi(optvalue);
                }
                else if (optname == "UseBook") {
                    use_book = (optvalue == "true" || optvalue == "1");
                }
                else if (optname == "BookDepth") {
                    book_depth_limit = std::stoi(optvalue);
                }
                else if (optname == "SyzygyPath") {
                    syzygy_path = optvalue;
                    if (!syzygy_path.empty() && syzygy_path != "<empty>") {
                        initSyzygy();
                    }
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
