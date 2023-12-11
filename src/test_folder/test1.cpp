#include <iostream>
#include <fstream>
#include <string>
#include <bits/stdc++.h>
#include <stdlib.h>
#include <map>
#include <iomanip>
#include <vector>
#include <utility>
#include <algorithm>
#include <float.h>
#include "Database.h"
#include "aux_fun.cpp"
#include "Z:\\anaconda3\\include\\Python.h"


using namespace std;

map<int, string> var_exp;                                      //记录性质中提取出的变量表达式作为命题
vector<string> var;                                            //存储性质中提取出的变量
map<string, string> var_type;                                  //记录头文件中各个变量名及变量类型

ifstream property_infile;                                      //待验证性质文件，以规定的形式编写:extract_var()
fstream var_store_outfile;                                     //存放性质中提取的变量(中间文件)
ifstream src_code_c;                                           //待测IP.c源文件
ifstream src_code_h;                                           //待测IP.h头文件
fstream klee_code;                                             //用于KLEE工具生成测试用例的代码文件


/*根据性质提取生成测试用例相关的变量及变量表达式，变量用于KLEE进行符号化生成测试用例，表达式用于为TRACE生成命题*/
void extract_var(){

    int count_var = 0, count_var_exp = 0;                       //记录提取的变量,及变量表达式数量
    map<string, int> pro;                                       //记录变量相关的表达式
    string IP_name = "Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\"; //IP路径
    string filename = IP_name + "IP_gyrochoose_property.txt";         //待处理的文件名
    property_infile.open(filename);
    if (!property_infile.is_open())		                           //判断文件是否成功打开
	{
		cout<<"Error opening file:modecontrol_property.txt"<<endl;
	}
    var_store_outfile.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\IP_gyrochoose_propos.txt", ios::app|ios::out|ios::in);
    while(!property_infile.eof()){
        string line, var_id, var_val;
        int begin_var, end_val;
        getline(property_infile, line);
        if(line.length()==0) continue;                             //空行则直接跳过
        for(int i=0; i<line.length(); i++){                        //遍历读入的待验证性质，记录出现过的变量
            if(line[i]=='=' || line[i]=='>' || line[i]=='<' || line[i]=='!'){
                if(line[i-1]=='-') continue;                       //处理蕴含运算符“->”情况
                if(line[i-1]=='>' || line[i-1]=='<' || line[i-1]=='!') continue;     //处理运算符">=""<="情况
                /*提取变量名*/
                int j = i;                                         //j表示"=/>/</!"的位置
                while(j>=0 && line[j-1]!=' '){
					string var_name;
					int bal = 0;
					if(line[j-1]==')'){
						var_name.insert(0,1,line[j-1]);
						j--;
						bal--;
						while(bal<=0 && line[j-1]!=' ' && j>0){
							j--;
							var_name.insert(0,1,line[j]);
							if(line[j]=='(') bal++;
							else if(line[j]==')') bal--;
						}
						if(bal>0) j++;
                        //if(bal<0) cout<<"性质文件格式输入错误"<<endl;
					}else{
						if(line[j-1]=='('){
							break;
						}
						j--;
						var_name.insert(0,1,line[j]);
					}
                }
                if(j<0){
                    cout<<"性质文件输入格式错误1\n"<<endl; 
                    return;
                }
                //提取变量名时对于next操作符单独处理
                begin_var = j;
                if(line.substr(begin_var, (i-begin_var)).find("next") != string::npos){
                    var_id =  line.substr(begin_var+5, (i-begin_var-6));
                }else{
                    var_id = line.substr(begin_var, (i-begin_var));
                }
                if(find(var.begin(), var.end(), var_id) == var.end()) var.push_back(var_id);    //重复变量，只记录一次                                       
                /*提取变量值*/
                if(line[i+1]=='='){                                  //处理“>=”,"<="情况
                    j = i+1;                
                }else{
                    j = i;
                }
                int k = j;
                int bal = 0, p = 0;
                string exp_val;
                if(line[k++]=='(') bal++;
                while(k<line.length() && bal>=0 && line[k]!=' '){
                    exp_val[p++] = line[k];
                    if(line[k]=='('){
                        bal++;
                    }else if(line[k]==')'){
                        bal--;
                    }
                    k++;
                }
                if(bal<0) k--;
                if(k>line.length()){
                    cout<<"性质文件输入格式错误2\n"<<endl; 
                    return;
                }
                end_val = k-1;
                var_val = line.substr(j+1, end_val-j);
                string temp = line.substr(begin_var, end_val-begin_var+1);      //当变量值为字符类型等时，如何解决？
                if(pro[temp] != 1){                                             //相同的变量表达式只存储一次
                    pro[temp] = 1;
                    var_exp[count_var_exp] = temp;
                    if(var_exp[count_var_exp]<var_exp[count_var_exp-1] && count_var_exp>0){ 
                        for(int k = count_var_exp; k>0; k--){                           //有序存储所有的表达式，便于后期判断命题的值
                            if(var_exp[k]<var_exp[k-1]){
                                string temp;
                                temp = var_exp[k];
                                var_exp[k] = var_exp[k-1];
                                var_exp[k-1] = temp;
                            }
                        }                       
                    }
                    count_var_exp++;    
                }                     
            }    
        }
    }
    // for(int i=0; i<count_var_exp; i++){                      //将提取的命题输入到输出文件中(每个提取的变量表达式对应一个命题)
    //     var_store_outfile<<var_exp[i]<<"\n";
    // }
    property_infile.close();
    var_store_outfile.close();
    return;
}

void KLEE_generate_testcase(){
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c");
    src_code_h.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.h");
    map<string, string> symbolic_var;//待符号化的变量<变量名，变量类型> 
    while(!src_code_h.eof()){
        string line;
        getline(src_code_h, line);
        if((line.find("int")!=string::npos || line.find("oat")!=string::npos) && line.find(";")!=string::npos){
            int type_s, type_e;
            if(line.find("int")!=string::npos){//siint等int型变量
                type_s = line.find("int") - 2;//定位变量类型
                type_e = line.find("int") + 4;
            }else{//float型变量
                type_s = line.find("oat") - 2;
                type_e = line.find("oat") + 4;
            }
            int var_s = type_e + 2;//定位变量名
            while(line[var_s]==' ' || line[var_s]=='\t') var_s++;
            int var_e = line.find(";") - 1;
            var_type[line.substr(var_s, var_e-var_s+1)] = line.substr(type_s, type_e-type_s+1);
        }
    }
    klee_code.open("Z:\\computer science\\SAM_DATA\\IP_attical\\klee_code.c",ios::app|ios::out|ios::in);
    klee_code<<"#include \"klee/klee.h\"\n"<<"#include <string.h>"<<endl;
    map<string, unint32> array;//标识数组：<数组名，数组最后一个数值下标>
    bool branch;            //标识整个IP实现中是否存在条件分支
    while(!src_code_c.eof()){
        string line;
        getline(src_code_c, line);
        klee_code<<line<<endl;
        if(line.find("if")!=string::npos){//定位IP中的分支条件(有可能不存在分支)
            find_symbolic_var(line, var_type, symbolic_var, array);
            branch = true;
        }
    }
    if(branch==false){//IP中无分支存在
        src_code_c.clear();//重新扫描文件提取变量
        src_code_c.seekg(0, ios::beg);
        while(!src_code_c.eof()){
            string line;
            getline(src_code_c, line);
            if(line.find(";")!=string::npos){
                find_symbolic_var(line, var_type, symbolic_var, array);
            }
        }
    }
    //数组大小确定
    for(auto it=array.begin(); it!=array.end(); it++){
        for(int i=0; i<var_exp.size(); i++){
            string len_of_array;
            len_of_array = "|"+it->first+"|";
            if(var_exp[i].find(len_of_array)!=string::npos){
                int len;
                len = extract_len(var_exp[i]);
                if(len>it->second) it->second = len-1;
                break;
            }    
        }
        for(auto it2=var_type.begin(); it2!=var_type.end(); it2++){
            if(it2->first.find(it->first)!=string::npos){
                klee_code<<it2->second<<" "<<it->first<<"["<<it->second+1<<"];"<<endl;
                break;
            }
        }   
    }
    string filename = get_filename("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c");
    klee_code<<filename<<" "<<filename<<"1={"<<endl;
    klee_code<<"\t.fun="<<filename<<"Fun,"<<endl;
    for(auto it=array.begin(); it!=array.end(); it++){
       klee_code<<"\t."<<it->first<<"=&"<<it->first<<"[0],"<<endl;
    }
    klee_code<<"};\n"<<endl; 
    klee_code<<"int main(){"<<endl;
    int count = 0;//辅助变量，用于符号化变量使用
    for(auto it=symbolic_var.begin(); it!=symbolic_var.end(); it++){
        klee_code<<"\t"<<it->second<<"* "<<"p"<<count<<";\n\t"<<it->second<<" "<<"p"<<count+1<<";\n";
        klee_code<<"\tp"<<count<<"= &"<<filename<<"1."<<it->first<<";\n";
        klee_code<<"\tklee_make_symbolic(&p"<<count+1<<", sizeof(p"<<count+1<<"), \""<<it->first<<"\");\n";
        klee_code<<"\tmemcpy(p"<<count<<", &p"<<count+1<<", sizeof("<<filename<<"1."<<it->first<<"));\n";
        count += 2;
        if(branch==false) klee_code<<"\tklee_assume("<<filename<<"1."<<it->first<<"!=0);\n"<<endl;
    }
    for(auto it=array.begin(); it!=array.end(); it++){
       klee_code<<"\tklee_make_symbolic("<<it->first<<", sizeof("<<it->first<<"), \""<<it->first<<"["<<it->second+1<<"]\");\n";
       if(branch==false) klee_code<<"\tklee_assume("<<it->first<<"[0]"<<"!=0);\n"<<endl;        //尽量避免生成全0的测试用例，但对全0测试用例要进行单独测试
    }
    klee_code<<"\tIPCALL("<<filename<<"1"<<");"<<endl;
    klee_code<<"}"<<endl;
    src_code_c.close();
    src_code_h.close();
}

int main(){

    KLEE_generate_testcase();
    for(auto it=var_type.begin(); it!=var_type.end(); it++){
        cout<<it->first<<" "<<it->second<<endl;
    }
}