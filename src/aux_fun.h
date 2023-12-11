#ifndef _AUX_FUN_H_
#define _AUX_FUN_H_
#include "Database.h"
#include <string>
#include <map>
#include <regex>
#include "Z:\\anaconda3\\include\\Python.h"

using namespace std;

/*�ж�ĳ�ļ��Ƿ���ڣ����ڼ�����true*/
bool isFileExists_ifstream(string &name);

/*�����ۼӲ�����Ŀǰֻ����sacheck�����Եļ��*/
string ADDSUM(string s, std::map<string, string> mp);

/*���ļ�·������ȡ�ļ���(����չ��)*/ 
string get_filename(string path);

/*�������ַ�������ȡ���±꣬���ַ���pbuff[14]����ȡ14*/ 
int extract_index(string s);

/*��һ�����ʽ����ȡ����:|pbuff|>17����ȡ17*/
int extract_len(string s);

/*��������֧�������ȡ���漰���ı����������������ͱ�������
string s��ʾ�����������֧��䣬vector<string> var��ʾ�Ӵ���֤��������ȡ���ı���*/ 
void find_symbolic_var(string s, map<string, string>var_type, map<string, string> &symbolic_var, map<string, unint32> &array);

/*����ǰ״̬����ֵ��ΪԼ����ӵ�z3Prover�����Contract���������*/
bool z3_result(string Py_filename);
#endif