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
map<string, string> const_var;                                 //记录变量中可能出现的常量及其值(初始给出)，常量不进行符号化

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
ofstream demo_file;                                           //存放待判断的添加了约束Contract文件

//待处理的contract等路径
string cp_path = "Z:\\computer science\\SAM_DATA\\IP_modeswitch\\";
//待处理的IP.c路径
string IP_cpath = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_ModeSwitch\\ModeSwitch.c";
//待处理的IP.h路径
string IP_hpath = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_ModeSwitch\\ModeSwitch.h";

/*根据性质提取生成测试用例相关的变量及变量表达式，变量用于KLEE进行符号化生成测试用例，表达式用于为TRACE生成命题*/
void extract_var(){
    
    int count_var = 0, count_var_exp = 0;                       //记录提取的变量,及变量表达式数量
    map<string, int> pro;                                       //记录变量相关的表达式
    //string filename = cp_path + "IP_unpack_property.txt";         //待处理的文件名
    //property_infile.open(filename);
    property_infile.open("Z:\\computer science\\SAM_DATA\\IP_modeswitch\\IP_modeswitch_property.txt");
    if (!property_infile.is_open())		                           //判断文件是否成功打开
	{
		cout<<"Error opening file:modecontrol_property.txt"<<endl;
	}
    //var_store_outfile.open((cp_path+"IP_unpack_propos.txt").c_str(), ios::app|ios::out|ios::in);
    var_store_outfile.open("Z:\\computer science\\SAM_DATA\\IP_modeswitch\\IP_modeswitch_propos.txt", ios::app|ios::out|ios::in);
    while(!property_infile.eof()){
        string line, var_id, var_val;
        int begin_var, end_val;
        getline(property_infile, line);
        if(line.length()==0) continue;                             //空行则直接跳过
        for(int i=0; i<line.length(); i++){                        //遍历读入的待验证性质，记录出现过的变量
            if(line[i]=='=' || line[i]=='>' || line[i]=='<' || line[i]=='!'){
                if(line[i-1]=='-' && line[i]=='>') continue;                       //处理蕴含运算符“->”情况
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
    for(int i=0; i<count_var_exp; i++){                      //将提取的命题输入到输出文件中(每个提取的变量表达式对应一个命题)
        var_store_outfile<<var_exp[i]<<"\n";
    }
    property_infile.close();
    var_store_outfile.close();
    return;
}

/*将变量符号化并调用KLEE生成测试用例*/
void KLEE_generate_testcase(){
    
    src_code_c.open(IP_cpath);
    src_code_h.open(IP_hpath);
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
    klee_code.open((cp_path+"klee_code.c").c_str(),ios::app|ios::out|ios::in);
    klee_code<<"#include \"klee/klee.h\"\n"<<"#include <string.h>"<<endl;
    map<string, unint32> array;//标识数组<数组名，数组大小>
    bool branch;               //标识整个IP实现中是否存在条件分支
    while(!src_code_c.eof()){
        string line;
        getline(src_code_c, line);
        klee_code<<line<<endl;
        if(line.find("if")!=string::npos || line.find("switch")!=string::npos){//定位IP中的分支条件(有可能不存在分支)
            find_symbolic_var(line, var_type, symbolic_var, array);
            branch = true;
        }
    }
    if(branch==false){//IP中无分支存在
        src_code_c.close();//重新扫描文件提取变量
        src_code_c.open(IP_cpath);
        while(!src_code_c.eof()){
            string line;
            getline(src_code_c, line);
            if(line.find(";")!=string::npos){
                find_symbolic_var(line, var_type, symbolic_var, array);
            }
        }
    }
    for(auto it=array.begin(); it!=array.end(); it++){
        for(int i=0; i<var_exp.size(); i++){
            string len_of_array;
            len_of_array = "I"+it->first+"I";
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
    string filename = get_filename(IP_cpath);
    klee_code<<filename<<" "<<filename<<"1={"<<endl;
    klee_code<<"\t.fun="<<filename<<"Fun,"<<endl;
    for(auto it=array.begin(); it!=array.end(); it++){
       klee_code<<"\t."<<it->first<<"=&"<<it->first<<"[0],"<<endl;
    }
    klee_code<<"};\n"<<endl; 
    klee_code<<"int main(){"<<endl;
    int count = 0;//辅助变量，用于符号化变量使用
    for(auto it=symbolic_var.begin(); it!=symbolic_var.end(); it++){
        if(const_var[it->first].length()!=0 || it->second.find("float")!=string::npos){
    		continue;
    	}
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
    return;
}

/*提取测试用例实际值的函数*/
void read_test_case(int index){                               
    test_case.clear();
    int begin_name, end_name;                               //定位变量名
    int begin_val, end_val;                                 //定位变量值
    int array_size = 0;                                     //如果其中有数组，记录数组大小
    unint32 val;
    string line;                                            //文件中的一行
    test_case_infile.open("Z:\\computer science\\SAM_DATA\\IP_modeswitch\\testcase_in"+to_string(index)+".txt");
    if (!test_case_infile.is_open())		                           //判断文件是否成功打开
	{
		cout<<"Error opening file:test_case_in.txt"<<endl;
		return;
	}
    string temp, NAME, VAL;                         //temp用于临时存储上一行的数据，便于后续查询;NAME,VAL记录变量名，变量值
    string array_name;
    while(!test_case_infile.eof()){
        getline(test_case_infile, line);                    //获取文件中单行数据
        begin_name = line.find("name");                     //定位变量名，变量值
        bool val_output;                                    //记录是否已经输出了val,用于输出没有"int"关键词的数据，通常是数组或者非数型变量
        if(begin_name != string::npos){                     //输出变量名
            begin_name += 7;                                //从“name”到变量名第一个字符距离为7个字符(固定)
            end_name = line.find("'", begin_name+1);
            NAME = line.substr(begin_name,(end_name-begin_name));
            if(NAME.find('[')!=string::npos){
                array_name = NAME;
            }
            val_output = false;                      
        }
        if(NAME.find('[')!=string::npos && array_size==0){ //提取数组大小
            getline(test_case_infile, line);
            if(line.find("size")!=string::npos){
                int op = line.find("size");
                op = op+6;
                string size = line.substr(op, line.length()-op);
                array_size = atoi(size.c_str());
            }
        }
        //若在程序中声明的变量是无符号型，则需要提取uint处的数据
        
        if(var_type[NAME].find("unint")!=string::npos){
            begin_val = line.find("uint");   
        }else{
            begin_val = line.find(" int");
            if(begin_val!=string::npos){
                begin_val++;  
            } 
        }                  
        if(begin_val != string::npos){                      //输出变量值
            begin_val += 6;
            end_val = line.find("\n", begin_val+1);
            VAL = line.substr(begin_val,(end_val-begin_val));
            test_case[NAME] = VAL;
            var_last_val[NAME] = VAL;
            val_output = true;
        }else if(line.find("text:")!=string::npos && val_output==false){ //"text:"是一个测试用例变量的末行；该部分用于处理测试用例中包括数组型数据时
            begin_val = temp.find("hex") + 8;
            VAL = temp.substr(begin_val, (temp.length()-begin_val));
            int mark = array_name.find('[');
            for(int i=0; i<array_size; i++){
                string name = array_name.substr(0,mark)+'['+to_string(i)+']';
                string val = to_string(stoul(VAL.substr(i*(VAL.length()/array_size), VAL.length()/array_size),nullptr,16));
                var_last_val[name] = val;
                test_case[name] = val;
            }
        }
        temp = line;                                                 
    }
    test_case_infile.close();
    return;
}

/*使用read_test_case函数读出的值，生成GDB调试的初始代码，用于生成执行日志*/
void generate_execu_log(){
    src_code_c.open(IP_cpath);
    init_code.open((cp_path+"gdb_debug_code.c").c_str(), ios::app|ios::out|ios::in);
    while(!src_code_c.eof()){     //将IP实现部分拷贝到用于生成执行日志的文件中
        string line;
        getline(src_code_c, line);
        init_code<<line<<endl;    
    }
    string filename = get_filename(IP_cpath);//文件名与IP名称，内部结构体名称一致
    map<string, string> var_temp;//暂时存放提取的测试用例中的非数组型数组
    int size = 0;//只用于结构体中的数组初始化
    string temp[100], array_name;
    for(auto it=test_case.begin(); it!=test_case.end(); it++){
        if(it->first.find('[')!=string::npos){
            int index = extract_index(it->first);
            temp[index] = it->second;
            size++;
            if(array_name.length()==0)array_name = it->first.substr(0, it->first.find('['));    
        }else{
            string var_name = it->first;
            string var_val = it->second;
            var_temp[var_name] = var_val;
        }
    }
    if(array_name.length()!=0){
        init_code<<"unint08 "<<array_name<<"["<<size<<"]={";
        for(int i=0; i<size; i++){
            init_code<<temp[i];
            if(i+1<size) init_code<<",";
        }
        init_code<<"};"<<endl;
    }
    init_code<<filename<<" "<<filename<<"1={"<<endl;//利用生成的测试用例初始化结构体中的数据，结构体名称为“文件名1”，例如“Fg333saCheck1”
    init_code<<"\t.fun="<<filename<<"Fun,"<<endl;
    for(auto it=var_type.begin(); it!=var_type.end(); it++){//单独初始化指针变量
        if(it->first.find("*")!=string::npos){
            init_code<<"\t."<<it->first.substr(1,it->first.length()-1)<<"="<<"&"<<it->first.substr(1,it->first.length()-1)<<"[0],"<<endl;
        }
    }
    if(array_name.length()!=0) init_code<<"\t."<<array_name<<"="<<"&"<<array_name<<"[0],"<<endl;
    //for(auto it=var_temp.begin(); it!=var_temp.end(); it++){
        //if(it->first.length()>0) init_code<<"\t."<<it->first<<"="<<it->second<<","<<endl;
    //}
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){
     	if(var_type[it->first].length()>0) init_code<<"\t."<<it->first<<"="<<it->second<<","<<endl;
    }
    init_code<<"};\n"<<endl;//结构体初始化完成
    init_code<<"int main(){"<<"\n"<<"\tIPCALL("<<filename<<'1'<<");"<<"\n}"<<endl;//定义main函数，调用IP
    src_code_c.close();
    init_code.close();
}

/*根据提取出的变量值，编写GDB自动化脚本*/
void generate_GDB_script(){
    string src_path = IP_cpath;
    string filename = get_filename(src_path);//提取文件名(无后缀)
    init_code.open((cp_path+"gdb_debug_code.c").c_str(), ios::app|ios::out|ios::in);
    if(!init_code.is_open()){
        cout<<"Error opening file:"<<filename<<endl;
    }
    GDB_script.open((cp_path+"gdb_script.gdb").c_str(),ios::app|ios::out|ios::in);
    int count_line = 0, count_bp = 0;                         //记录程序读入的行数,设置的断点数
    GDB_script<<"set logging on trace.txt"<<"\n"<<"b "<<"gdb_debug_code.c:main"<<endl;
    for(auto it=var_type.begin(); it!=var_type.end(); it++){//在IP初始结构体中出现的变量使用display关键字即可，未在IP中定义，但在命题中出现的需要单独打印
        if(it->first.find("*")!=string::npos){//指针类型变量，带有指针类型的变量(一般为数组)，可以根据Contract的Assumption初始化
            string array_name = it->first.substr(1,it->first.length()-1);
            int size;
            if(array_name=="W") size = 3;
            else if(array_name=="Gi") size = 2;
            for(int i=0; i<size; i++){
                if(it->second.find("siint")!=string::npos) GDB_script<<"\tdisplay/d "<<array_name<<"["<<i<<"]"<<endl;
                else if(it->second.find("unint")!=string::npos) GDB_script<<"\tdisplay/u "<<array_name<<"["<<i<<"]"<<endl;
                else if(it->second.find("float")!=string::npos) GDB_script<<"\tdisplay/f "<<array_name<<"["<<i<<"]"<<endl;
            }
        }else if(it->first.find("[")!=string::npos){//数组型变量
                if(it->first.find("][")!=string::npos){//多维数组
                    
                }else{//一维数组
                    int array_size = extract_index(it->first);
                    for(int i=0; i<array_size; i++){
                        if(it->second.find("siint")!=string::npos) GDB_script<<"\tdisplay/d "<<filename<<"1."<<it->first.substr(0, it->first.find("[")+1)<<i<<"]"<<endl;
                        else if(it->second.find("unint")!=string::npos) GDB_script<<"\tdisplay/u "<<filename<<"1."<<it->first.substr(0, it->first.find("[")+1)<<i<<"]"<<endl;
                        else if(it->second.find("float")!=string::npos) GDB_script<<"\tdisplay/f "<<filename<<"1."<<it->first.substr(0, it->first.find("[")+1)<<i<<"]"<<endl;
                    }
                }
        }else{
            if(it->second.find("siint")!=string::npos){
                GDB_script<<"\tdisplay/d "<<filename<<"1."<<it->first<<endl;
            }else if(it->second.find("float")!=string::npos){
                GDB_script<<"\tdisplay/f "<<filename<<"1."<<it->first<<endl;
            }else if(it->second.find("unint")!=string::npos){
            	GDB_script<<"\tdisplay/u "<<filename<<"1."<<it->first<<endl;
            }  
        }
    }
    while(!init_code.eof()){
        string code;
        getline(init_code, code);
        count_line++;
        for(int i=0; i<var.size(); i++){
            if(code.find(var[i])!=string::npos && (code.find('=')!=string::npos || code.find('+')!=string::npos || code.find('-')!=string::npos)){//如果该行代码中存在提取出的变量值
                if((code.find('(')<code.find(var[i]) && code.find(';')==string::npos) | code.find('{')!=string::npos) continue;//该行为条件判断行,不需要打断点           
                if(code.find(" .") != string::npos) continue;      //某些结构体变量初始化的过程
                count_bp++;
                GDB_script<<"b "<<"gdb_debug_code.c"<<":"<<count_line+1<<"\n"<<"\tcommands "<<count_bp<<endl;
                for(int j=0; j<var.size(); j++){//IP中不存在初始定义的变量单独打印
                    if(var_type[var[j]].length()==0){
                        smatch results;
                        string pattern("\\|[a-zA-Z]+\\|");
                        regex r(pattern);
                        string::const_iterator itb = var[j].begin();//定义迭代器，用于访问整个字符串
                        string::const_iterator ite = var[j].end();
                        if(regex_search(itb,ite,results,r)){
                           string temp = results[0];
                           temp = temp.substr(1,temp.length()-2);//提取数组名部分
                           if(var_type["*"+temp].length()>0)  GDB_script<<"\tprintf\""<<var[j]<<" = %d\\n\", sizeof("<<temp<<")/sizeof("<<temp<<"[0]),"<<endl;
                           else GDB_script<<"\tprintf\"1: "<<var[j]<<" = %d\\n\", sizeof("<<filename<<"1."<<temp<<")/sizeof("<<filename<<"1."<<temp<<"[0]),"<<endl; 
                        }
                    }
                }
                GDB_script<<"\tcontinue"<<"\n"<<"end"<<endl;
                break;    
            }
        }
        if(code.find('}')==0 && count_bp>0){			//保证在IP实现返回前所有的变量都得到更新
            GDB_script<<"b "<<"gdb_debug_code.c"<<":"<<count_line<<"\n"<<"\tcommands "<<count_bp+1<<endl;
            GDB_script<<"\tcontinue"<<"\n"<<"end"<<endl;
            break;
        }
    }
    GDB_script<<"run"<<endl;
    GDB_script.close();
    src_code_c.close();
    init_code.close();
    //以下用于调用GDB去调试上述生成的初始化后的IP，并生成程序执行日志
    //system("gcc -g gdb_debug_code.c -o gdb_debug_code");
    //system("gdb gdb_debug_code");
    //system("source gdb_script.gdb");  
}

/*判断etf路径文件的活动属性中命题的正误*/
void judge_proposition(map<string, pair<string, string>> &next, int count){      //count记录当前执行路径的长度
    
    map<string, bool> next_in;                                  //记录存在next的变量，这些变量的赋值需要单独处理
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){        //定义执行日志中变量值迭代器
        for(int j=0; j<var_exp.size()-1; j++){
            if(var_exp[j].find(it->first)==string::npos) continue;                       
            if(var_exp[j].find(("next("+it->first+")").c_str())!=string::npos){  //找到了关于该变量的next判断表达式
                next_in[it->first] = true;
                if(it->first.find("[")!=string::npos){//数组变量
                    demo_file<<"s.add("<<it->first<<"=="<<next[it->first].first<<")"<<endl;
                    string array_name, array_index;//表示数组名和数组下标
                    array_name = it->first.substr(0, it->first.find("["));
                    array_index = it->first.substr(it->first.find("["), it->first.length()-it->first.find("["));
                    if(next[it->first].second.length()!=0){
                        demo_file<<"s.add("<<array_name<<"_next"<<array_index<<"=="<<next[it->first].second<<")"<<endl;
                        break;
                    }else{
                        demo_file<<"s.add("<<array_name<<"_next"<<array_index<<"=="<<next[it->first].first<<")"<<endl;
                        break;
                    }
                }else{
                    demo_file<<"s.add("<<it->first<<"=="<<next[it->first].first<<")"<<endl;
                    if(next[it->first].second.length()!=0){   
                        demo_file<<"s.add("<<it->first<<"_next=="<<next[it->first].second<<")"<<endl;
                        break;
                    }else{
                        demo_file<<"s.add("<<it->first<<"_next=="<<next[it->first].first<<")"<<endl;
                        break;
                    }
                }
            }  
        }
    }
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){        //定义执行日志中变量值迭代器
        if(next_in[it->first]==false) demo_file<<"s.add("<<it->first<<"=="<<it->second<<")"<<endl;
    }
    demo_file<<"print(s.check())"<<endl;
    demo_file<<"\n"<<endl;
    propos[count] = z3_result("demo.py");
    //cout<<boolalpha<<propos[count]<<endl;
    //z3_file.close();
    return;
}

/*提取执行日志,并转换为etf路径文件*/
void read_trace(int index){//index指示当前处理的trace序号

    string line;
    int num_bp = 0;                                   //通过记录执行日志打印的断点数记录生成的路径长度
    bool last_line = false;                           //用于记录是否读到文件末尾，与next操作符关联          
    trace_infile.open((cp_path+"trace"+to_string(index)+".txt").c_str(), ios::app|ios::out|ios::in);
    trace_outfile.open((cp_path+"TRACE"+to_string(index)+".etf").c_str(), ios::app|ios::out|ios::in);
    z3_file.open("Z:\\computer science\\VScode\\vscode_project\\project\\ModeControl\\SAM_auto\\src\\ModeSwitch.py"); //打开z3Prover的文件
    demo_file.open("Z:\\computer science\\VScode\\vscode_project\\project\\ModeControl\\SAM_auto\\src\\demo.py",ios::trunc|ios::out|ios::in);
    while(!z3_file.eof()){
        getline(z3_file, line);
        demo_file<<line<<endl;
    }
    demo_file.seekp(0, ios::end);                      //标识文件末尾位置
    streampos sp = demo_file.tellp();                     
    if(!trace_outfile.is_open())		                        //判断文件是否成功打开
	{
		cout<<"Error opening file:trace.txt"<<endl;
	}
    trace_outfile<<"TU MILLISECONDS\n"<<"R 0 100.0 false;\n";
    map<string, pair<string, string>> next;                                  //first存放当前变量值，second存放下个状态变量值，用于之后比较
    while(!trace_infile.eof()){              
        getline(trace_infile, line);
        if((line[0]-'0')<10 && (line[0]-'0')>0 && line.find(':')==string::npos){      //定位断点的位置，以行开头为数字作为识别标识
            getline(trace_infile, line);
            string para_name, para_val;                         //存储参数名，参数值
            while(line.find(":")!=string::npos && line.find("exited")==string::npos){
                if(line.find('=')==string::npos) break;
                int j = line.find("=");
                if(line.find('.')!=string::npos && line.find(".")<j){
                    int aux1;                 //辅助记录变量名的位置，对变量名进行简化，去除掉所在的结构体或者类(也可以根据需要保留)
                    aux1 = line.find('.');
                    para_name = line.substr(aux1+1, j-aux1-2);
                    para_val = line.substr(j+2, line.length()-(j+2));
                }else{
                    int aux2 = line.find(':');
                    if(line.find("/f")!=string::npos || line.find("/d")!=string::npos || line.find("/u")!=string::npos) para_name = line.substr(aux2+5, j-aux2-6);
                    else para_name = line.substr(aux2+2, j-aux2-3);
                    para_val = line.substr(j+2, line.length()-(j+2));
                }
                var_last_val[para_name] = para_val;                 //执行日志中最新的变量值存入 
                if(next[para_name].first.length()==0){
                    next[para_name].first = para_val;
                }else{
                    next[para_name].second = para_val;
                }
                getline(trace_infile, line);
            }
            if(line.find("exited") != string::npos){
            	judge_proposition(next, num_bp);
                if(index==9) cout<<num_bp<<endl;
                num_bp++;
            	break;
            } 
            judge_proposition(next, num_bp);
            demo_file.seekp(sp, ios::beg);
            num_bp++;
            if(index==9) cout<<num_bp<<endl;
        }                                        
    }
    for(int i=0; i<num_bp; i++){
        trace_outfile<<"C "<<i<<" ";
        trace_outfile<<fixed<<setprecision(1)<<1.0*i<<" "<<1.0*(i+1)<<" 0 100.0;";//输出活动的定义  
        trace_outfile<<boolalpha<<"p"<<"="<<propos[i];
        trace_outfile<<"\n";
    }
    trace_outfile<<"S 0; name = s1\n"<<"F 0 0 "<<1.0*num_bp<<" 1.0 0.0 0.0"<<endl;
    demo_file.close();
    z3_file.close();
    trace_infile.close();
    trace_outfile.close();
    return;
}

int main(){
    
    var_last_val.clear();
    /*Fg333saUnPack
    const_var["dtime"] = "0.404755";
	var_last_val["dtime"] = "0.404755";
    */
    // time_t be = clock();
    extract_var();
    //KLEE_generate_testcase();
    // 
    // generate_execu_log();
    // generate_GDB_script();
    for(int i=1; i<=9; i++){
        read_test_case(i);
        read_trace(i);
    }
    // time_t ed = clock();
    // cout<<(double)(ed-be)/CLOCKS_PER_SEC<<"s"<<endl;
    return 0;
}