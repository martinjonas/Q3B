#pragma once

#include <string>
#include <iostream>
#include <mutex>

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

public:
    static void Log(const std::string&, const std::string&, const int, const LogType& type = LogType::INFO);
    static void SetVerbosity(const unsigned int verbosityLevel)
    {
	m_verbosityLevel = verbosityLevel;
    }
};
