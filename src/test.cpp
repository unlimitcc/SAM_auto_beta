/*本程序用于从KLEE生成的测试用例文件中提取具体的值，并依据测试用
例生成执行日志，之后将执行日志转换为etf路径文件*/
#include <iostream>
#include <fstream>
#include <string>
#include <bits/stdc++.h>
#include <stdlib.h>
#include <cstdlib>
#include <map>
#include <iomanip>
#include <vector>
#include <utility>
#include <algorithm>
#include <float.h>
#include <thread>
#include <future>
#include <sstream>
#include <chrono>
#include "Database.h"
#include "aux_fun.h"
#include "Z:\\anaconda3\\include\\Python.h"

using namespace std;

map<string, string> test_case;                                 //记录提取出的测试用例
map<int, string> var_exp;                                      //记录性质中提取出的变量表达式作为命题
vector<string> var;                                            //存储性质中提取出的变量
map<string, string> op;                                        //存储性质中的时序运算符与TRACE工具中时序运算符对应关系(需初始化)
map<string, string> execu_log;                                 //记录执行日志中提取的变量与变量值
bool propos[10010];                                            //记录TRACE中claim的命题值
map<string, string> var_last_val;                              //记录当前程序中各个变量的最新值,(需要初始化的过程)
map<string, string> var_type;                                  //记录头文件中各个变量名及变量类型
map<string, bool> const_var;                                   //记录变量中可能出现的常量及其值(初始给出)，常量不进行符号化

ifstream property_infile;                                      //待验证性质文件，以规定的形式编写:extract_var()
fstream var_store_outfile;                                     //存放性质中提取的变量(中间文件)
fstream TRACE_property;                                        //TRACE工具性质文件
ifstream test_case_infile;                                     //测试用例源文件:read_test_case()        
fstream trace_infile;                                          //GDB生成的程序执行日志:read_trace()
fstream trace_outfile;                                         //转换后的TRACE路径文件
fstream GDB_script;                                            //GDB自动化脚本
ifstream src_code_c;                                           //待测IP.c源文件
ifstream src_code_h;                                           //待测IP.h头文件
fstream klee_code;                                             //用于KLEE工具生成测试用例的代码文件
fstream init_code;                                             //使用KLEE生成的测试用例初始化后的IP
ifstream z3_file;                                              //使用z3Prover求解运行时验证中每个执行路径节点contract的正确性
//fstream demo_file;                                           //存放待判断的添加了约束Contract文件

//待处理的contract等路径
string cp_path = "Z:\\computer science\\SAM_DATA\\IP_unpack\\";
//待处理的IP.c路径
string IP_cpath = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_Fg333saUnPack\\Implement\\Fg333saUnPack.c";
//待处理的IP.h路径
string IP_hpath = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_Fg333saUnPack\\Implement\\Fg333saUnPack.h";



int main(){
    
    ofstream demo_file("Z:\\computer science\\VScode\\vscode_project\\project\\ModeControl\\SAM_auto\\src\\demo1.py",ios::out|ios::in);
    demo_file.seekp(0, ios::end);
    streampos sp = demo_file.tellp();
    for(int i=0; i<7; i++){
        demo_file<<i<<endl;
        demo_file.seekp(sp, ios::beg);
    }
    return 0;
}