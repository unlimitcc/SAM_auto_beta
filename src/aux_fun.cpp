//该文件记录main.cpp中调用的辅助函数，其功能去整个自动化过程不直接相关
#include <iostream>
#include <fstream>
#include "aux_fun.h"

using namespace std;

bool isFileExists_ifstream(std::string& name) {
    
    std::ifstream f(name.c_str());
    return f.good();
}

string ADDSUM(string s, map<string, string>mp){
    int p = 1, end=1;//p是栈指针，用于提取整个ADDSUM表达式
    while(p>0){
        if(s[end]=='('){
            p++;
        }else if(s[end]==')'){
            p--;
        }
        end++;
    }                                                        
    string s_add = s.substr(0, end);              //确定整个累加式的范围
    int begin = 1;
    while(s_add[begin]!=')') begin++;               //提取累加式的待计算表达式部分
    string s_add_cal = s_add.substr(begin+1, s_add.length()-begin-2);
    int range = s_add.find('-');
    int st = range, ed = range;
    while(s_add[st]!=':') st--;
    while(s_add[ed]!=')') ed++;
    siint32 top = atoi(s_add.substr(st+1, range-st-1).c_str());
    siint32 down = atoi(s_add.substr(range+1, ed-range).c_str());
    int be = st;
    while(s_add[be]!='(') be--;
    string var_name = s_add.substr(be+1,st-be-1);
    string s_trans;                                         //记录转换后的字符串
    string temp;                                            //记录将累加式转换后的字符串
    smatch results;
    string pattern(var_name);//用于匹配非数组变量名的模板
    regex r(pattern);
    string::const_iterator itb = s_add_cal.begin();//定义迭代器，用于访问整个字符串
    string::const_iterator ite = s_add_cal.end();
    for(int i=top; i<=down; i++){
        string temp_s_add_cal = s_add_cal;
        while(s_add_cal.find(var_name)!=string::npos && regex_search(itb, ite, results, r)){
            s_add_cal.replace(s_add_cal.find(var_name), var_name.length(), to_string(i));
        }
        temp += s_add_cal;
        if(i<down) temp += '+';
        s_add_cal = temp_s_add_cal;
    }
    for(auto it=mp.begin(); it!=mp.end(); it++){
        while(temp.find(it->first)!=string::npos){
            temp.replace(temp.find(it->first), it->first.length(), it->second);
        }
    }
    s_trans = s.replace(0, s_add.length(), temp);
    return s_trans;
}

string get_filename(string path){//path表示文件所在的绝对路径
    int st_name = path.find_last_of("\\")+1; //标识文件名的起始位置
    int ed_name = path.find_last_of('.'); //标识文件名的末尾位置
    string filename = path.substr(st_name, ed_name-st_name);
    return filename;
}

int extract_index(string s){
    int r = s.find(']');
    int l = s.find('[');
    string index = s.substr(l+1, r-l-1);
    return atoi(index.c_str());
}

int extract_len(string s){
    int len;
    smatch results;
    string pattern("[0-9]+");//用于数字
    regex r(pattern);
    string::const_iterator itb = s.begin();//定义迭代器，用于访问整个字符串
    string::const_iterator ite = s.end();
    string temp;
    while(regex_search(itb, ite, results, r)){
        temp = results[0];
        len = stoi(temp);
        break;
    }
    return len;
}

void find_symbolic_var(string s, map<string, string>var_type, map<string, string> &symbolic_var, map<string, unint32> &array){
    smatch results;
    string pattern1("[A-Za-z0-9_]+");//用于匹配非数组变量名的模板
    string pattern2("[A-Za-z0-9]+\\[[0-9a-z]+\\]");//用于匹配数组变量名的模板
    regex r1(pattern1);
    regex r2(pattern2);
    string::const_iterator itb = s.begin();//定义迭代器，用于访问整个字符串
    string::const_iterator ite = s.end();
    string temp;
    while(regex_search(itb, ite, results, r2)){//匹配数组类型
        temp = results[0];
        string name = temp.substr(0, temp.find('['));
        if(array[name]<extract_index(temp)) array[name] = extract_index(temp);
        itb = results[0].second;
    }
    itb = s.begin();
    while(regex_search(itb, ite, results, r1)){//匹配普通变量类型
        temp = results[0];
        for(auto it=var_type.begin(); it!=var_type.end(); it++){
            if(it->first==temp){
                symbolic_var[temp] = var_type[temp];
                break;
            }
            //cout<<temp<<" "<<it->first<<endl;
        }
        itb = results[0].second;
    }
    return;
}

bool z3_result(string Py_filename){
    char buffer[100];
	FILE* fp;
	string com = "python " + Py_filename;
	fp = popen(com.c_str(), "r");
	if(fp == NULL){
		printf("Failed to run command\n");
		exit(1);
	}
	fgets(buffer, sizeof(buffer), fp);
    string result = buffer;
	pclose(fp);
    if(result.find("unsat")!=string::npos){
        return false;
    }else{
        return true;
    }
}