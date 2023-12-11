#ifndef _AUX_FUN_H_
#define _AUX_FUN_H_
#include "Database.h"
#include <string>
#include <map>
#include <regex>
#include "Z:\\anaconda3\\include\\Python.h"

using namespace std;

/*判断某文件是否存在，存在即返回true*/
bool isFileExists_ifstream(string &name);

/*处理累加操作，目前只用于sacheck中属性的检查*/
string ADDSUM(string s, std::map<string, string> mp);

/*从文件路径中提取文件名(无扩展名)*/ 
string get_filename(string path);

/*从数组字符串中提取出下标，例字符串pbuff[14]中提取14*/ 
int extract_index(string s);

/*从一个表达式中提取数字:|pbuff|>17中提取17*/
int extract_len(string s);

/*从条件分支语句中提取出涉及到的变量，包括变量名和变量类型
string s表示读入的条件分支语句，vector<string> var表示从待验证属性中提取出的变量*/ 
void find_symbolic_var(string s, map<string, string>var_type, map<string, string> &symbolic_var, map<string, unint32> &array);

/*将当前状态变量值作为约束添加到z3Prover后，求解Contract的满足情况*/
bool z3_result(string Py_filename);
#endif