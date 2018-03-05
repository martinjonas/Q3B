#include "Logger.h"

int Logger::m_verbosityLevel = -1;
std::mutex Logger::m;

std::string logTypeToStr(const LogType& type)
{
    switch (type)
    {
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

void Logger::Log(const std::string& module, const std::string& message, const int verbosity, const LogType& type)
{
    if (verbosity <= m_verbosityLevel)
    {
	std::unique_lock<std::mutex> lk(m);
	std::cout << "[" << logTypeToStr(type) << "] " << module << ": " << message << std::endl;
    }
}
