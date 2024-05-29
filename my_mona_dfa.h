#ifndef __MY_MONA_DFA__
#define __MY_MONA_DFA__
#include <iostream>
#include <fstream>
#include <vector>
#include <assert.h>
#include <string>
using namespace std;

int string2int(string s)
{
    int res = 0;
    for (int i = 0; i < s.size(); i++)
    {
        res = res * 10 + s[i] - '0';
    }
    return res;
}

void read_intlist_from_string(string &s, vector<int> &res)
{
    int i = 0;
    while (i < s.size())
    {
        while (i < s.size() && s[i]==' ') i++;
        if (i == s.size()) break;
        int j = i;
        while (j < s.size() && s[j] != ' ') j++;
        res.push_back(string2int(s.substr(i, j - i)));
        i = j;
    }
}

bool isEnd(int *arr)
{
    return arr[0] == -1 && arr[2] == 0;
}

struct MyMonaDFA{
    int trans_num;
    int states_num;
    int vars_num;           // don't use it actually
    int initial_stateid;
    vector<int> final;      // type of each state
    vector<int> behaviour;  // first move of each state
    vector<vector<int>> bdd;     // transition array
    string filename;

    void readMyMonaDFA_core()
    {
        string s;
        char ch;
        int line_num = 0;
        ifstream inFile(filename, ios::in | ios::binary);
        bool continue_flag = true;
        while(continue_flag)
        {
            line_num++; // start from 1
            string line_pres[] = {
                "",
                "MONA DFA",
                "number of variables: ",
                "variables: ",
                "orders: ", // NOT USED
                "states: ",
                "initial: ",
                "bdd nodes: ",
                "final: ",
                "behaviour: ",
                "bdd:",
            };
            string &curline_pre = line_pres[line_num];

            if (line_num < 11)
            {
                getline(inFile, s);
                assert(s.substr(0, curline_pre.size()) == curline_pre);
                s = s.substr(curline_pre.size());
                switch (line_num)
                {
                    case 2:
                        vars_num = string2int(s);
                        break;
                    case 5:
                        states_num = string2int(s);
                        break;
                    case 6:
                        initial_stateid = string2int(s);
                        break;
                    case 7:
                        trans_num = string2int(s);
                        break;
                    case 8:
                        read_intlist_from_string(s, final);
                        break;
                    case 9:
                        read_intlist_from_string(s, behaviour);
                        break;
                    case 10:
                        /* read transitions */
                        int x, l, r;
                        for (int i = 0; i < trans_num; i++) {
                            cin >> x >> l >> r;
                            bdd.push_back({x, l, r});
                        }
                        /* last line*/
                        cin >> s;
                        assert(s.substr(0,3) == "end");
                        continue_flag = false;
                        break;
                    default:
                        // do nothing
                        break;
                }
            }
        }
        inFile.close();
    }

    void *readMyMonaDFA(string dfa_filename)
    {
        filename = dfa_filename;
        // FILE* original_stdin = stdin;
        // stdin = fopen(dfa_filename.c_str(), "r");
        // === real code BEGIN
        readMyMonaDFA_core();
        // === real code END
        // fclose(stdin);
        // stdin = original_stdin;
    }
};

#endif