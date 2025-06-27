#include <iostream>
#include <fstream>
#include <chrono>
#include "nlohmann/json.hpp"
#include "chess.hpp"

using json = nlohmann::json;
using namespace chess;


std::string formatPGNLine(const std::string& moveListString, int startMoveNumber = 1) {
    std::istringstream iss(moveListString);
    std::vector<std::string> moves;
    std::string move;

    while (iss >> move) {
        moves.push_back(move);
    }

    std::ostringstream oss;
    int moveNum = startMoveNumber;

    for (size_t i = 0; i < moves.size(); ++i) {
        if (i % 2 == 0) {
            oss << moveNum << ". ";
        }
        oss << moves[i] << " ";
        if (i % 2 == 1) {
            moveNum++;
        }
    }

    return oss.str();
}


class ChessPuzzleSolver {
private:
    std::pair<int, std::string> minimax(Board& board, int depth, bool maximizing) {
    auto gameOver = board.isGameOver();
    if (gameOver.first == GameResultReason::CHECKMATE) {
        return {maximizing ? -1 : 1, ""};
    }
    if (gameOver.first != GameResultReason::NONE || depth == 0) {
        return {0, ""};
    }

    Movelist moves;
    movegen::legalmoves(moves, board);

    if (maximizing) {
        for (const Move& move : moves) {
            std::string moveSan = uci::moveToSan(board, move);
            board.makeMove(move);
            auto [res, seq] = minimax(board, depth - 1, false);
            board.unmakeMove(move);
            if (res == 1) {
                return {1, moveSan + " " + seq};
            }
        }
        return {0, ""};
    } else {
        std::string bestLine;
        for (const Move& move : moves) {
            std::string moveSan = uci::moveToSan(board, move);
            board.makeMove(move);
            auto [res, seq] = minimax(board, depth - 1, true);
            board.unmakeMove(move);
            if (res != 1) {
                return {0, ""};
            bestLine = moveSan + " " + seq;
        }
        return {1, bestLine};
    }


}


public:

    void solvePuzzlesFromJson(const std::string& filename, int mateInMoves) {
        std::ifstream file(filename);
        json j;
        file >> j;

        int solved = 0;
        auto start = std::chrono::high_resolution_clock::now();

        for (auto& [fen, _] : j.items()) {
            Board board(fen);
            auto [res, solution] = minimax(board, mateInMoves * 2 - 1, true);
            if (res == 1) {
                std::string pgn = formatPGNLine(solution);
                std::string expected = _.get<std::string>()+' '; 

                bool correct = (pgn == expected);
                if (correct) solved++;
                
                std::cout << fen << "\n" << pgn << " ___ " << expected << "\n\n";
            }
        }


        auto end = std::chrono::high_resolution_clock::now();
        auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

        std::cout << "Solved: " << solved << "/" << j.size()
                  << " (" << (100.0 * solved / j.size()) << "%)\n";
        std::cout << "Time: " << ms.count() << "ms\n";
    }
};

int main() {
    ChessPuzzleSolver solver;
    solver.solvePuzzlesFromJson("mate_in_4.json", 4);
    return 0;
}
