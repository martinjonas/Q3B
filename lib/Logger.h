#pragma once

#include <string>
#include <iostream>
#include <mutex>
#include <chrono>

enum LogType
{
    WARNING,
    INFO,
    ERROR
};

class Logger
{
private:
    static int m_verbosityLevel;
    static std::mutex m;
    static std::chrono::time_point<std::chrono::high_resolution_clock> startTime;

public:
    static void Log(const std::string&, const std::string&, const int, const LogType& type = LogType::INFO);
    static void SetVerbosity(const unsigned int verbosityLevel)
    {
	m_verbosityLevel = verbosityLevel;
    }

    static unsigned int GetVerbosity()
    {
	return m_verbosityLevel;
    }
};
