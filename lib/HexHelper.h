#ifndef HEXHELPER_H
#define HEXHELPER_H

#include <sstream>

class HexHelper
{
private:
    static const char *hex_char_to_bin(char c)
    {
        // TODO handle default / error
        switch (toupper(c)) {
        case '0':
            return "0000";
        case '1':
            return "0001";
        case '2':
            return "0010";
        case '3':
            return "0011";
        case '4':
            return "0100";
        case '5':
            return "0101";
        case '6':
            return "0110";
        case '7':
            return "0111";
        case '8':
            return "1000";
        case '9':
            return "1001";
        case 'A':
            return "1010";
        case 'B':
            return "1011";
        case 'C':
            return "1100";
        case 'D':
            return "1101";
        case 'E':
            return "1110";
        case 'F':
            return "1111";
        default:
            return "0000";
        }
    }

public:
    static std::string hex_str_to_bin_str(const std::string &hex)
    {
        // TODO use a loop from <algorithm> or smth
        std::string bin;
        for (unsigned i = 0; i != hex.length(); ++i)
            bin += hex_char_to_bin(hex[i]);
        return bin;
    }

    static unsigned int get_numeral_value(const std::string &numeralString)
    {
        const std::string prefix = numeralString.substr(0, 2);
        const std::string valueString = numeralString.substr(2);

        std::stringstream ss;
        unsigned int value;

        if (prefix == "#x") {
            ss << std::hex << valueString;
            ss >> value;
        } else if (prefix == "#b") {
            value = std::stoull(valueString, 0, 2);
        } else {
            std::cout << "Invalid BV prefix in: " << numeralString << std::endl;
            std::cout << "unknown" << std::endl;
            exit(1);
        }

        return value;
    }
};

#endif // HEXHELPER_H
