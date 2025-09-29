#include "Logger.h"

int Logger::m_verbosityLevel = 0;
std::mutex Logger::m;
std::chrono::time_point<std::chrono::high_resolution_clock> Logger::startTime =
    std::chrono::high_resolution_clock::now();

std::string logTypeToStr(const LogType &type)
{
    switch (type) {
    case LogType::WARNING:
        return "Warning";
    case LogType::INFO:
        return "Info";
    case LogType::ERROR:
        return "Error";
    default:
        abort();
    }
}

void Logger::Log(const std::string &module, const std::string &message,
                 const int verbosity, const LogType &type)
{
    if (verbosity <= m_verbosityLevel) {
        std::chrono::duration<double> time =
            std::chrono::high_resolution_clock::now() - startTime;
        std::unique_lock<std::mutex> lk(m);
        std::cout << "[" << logTypeToStr(type) << ", " << time.count() << "s] "
                  << module << ": " << message << std::endl;
    }
}
