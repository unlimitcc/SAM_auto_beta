/*本程序用于从KLEE生成的测试用例文件中提取具体的值，并依据测试用
例生成执行日志，之后将执行日志转换为etf路径文件*/
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
#include "aux_fun.h"
#include "Z:\\anaconda3\\include\\Python.h"

using namespace std;

map<string, string> test_case;                                 //记录提取出的测试用例
map<int, string> var_exp;                                      //记录性质中提取出的变量表达式作为命题
vector<string> var;                                            //存储性质中提取出的变量
map<string, string> op;                                        //存储性质中的时序运算符与TRACE工具中时序运算符对应关系(需初始化)
map<string, string> execu_log;                                 //记录执行日志中提取的变量与变量值
bool propos[20][101];                                          //记录TRACE中claim的命题值
map<string, string> var_last_val;                              //记录当前程序中各个变量的最新值,(需要初始化的过程)
map<string, string> var_type;                                  //记录头文件中各个变量名及变量类型

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
    string IP_name = "Z:\\computer science\\SAM_DATA\\IP_modeswitch\\"; //IP路径
    string filename = IP_name + "IP_modeswitch_property.txt";         //待处理的文件名
    property_infile.open(filename);
    if (!property_infile.is_open())		                           //判断文件是否成功打开
	{
		cout<<"Error opening file:modecontrol_property.txt"<<endl;
	}
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
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_ModeSwitch\\ModeSwitch.c");
    src_code_h.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_ModeSwitch\\ModeSwitch.h");
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
    klee_code.open("Z:\\computer science\\SAM_DATA\\IP_modeswitch\\klee_code.c",ios::app|ios::out|ios::in);
    klee_code<<"#include \"klee/klee.h\"\n"<<"#include <string.h>"<<endl;
    map<string, unint32> array;//标识数组<数组名，数组大小>
    bool branch;               //标识整个IP实现中是否存在条件分支
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
    string filename = get_filename("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_ModeSwitch\\ModeSwitch.c");
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
            begin_val = line.find("int");
            if(line[begin_val-1]=='u') continue;                //防止定位到“uint”
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
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c");
    init_code.open("Z:\\computer science\\SAM_DATA\\IP_attical\\gdb_debug_code.c", ios::app|ios::out|ios::in);
    while(!src_code_c.eof()){     //将IP实现部分拷贝到用于生成执行日志的文件中
        string line;
        getline(src_code_c, line);
        init_code<<line<<endl;    
    }
    string filename = get_filename("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c");//文件名与IP名称，内部结构体名称一致
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
    for(auto it=var_type.begin(); it!=var_type.end(); it++){
        if(it->first.find("*")!=string::npos){
            init_code<<"\t."<<it->first.substr(1,it->first.length()-1)<<"="<<"&"<<it->first.substr(1,it->first.length()-1)<<"[0],"<<endl;
        }
    }
    if(array_name.length()!=0) init_code<<"\t."<<array_name<<"="<<"&"<<array_name<<"[0],"<<endl;
    for(auto it=var_temp.begin(); it!=var_temp.end(); it++){
        if(it->first.length()>0) init_code<<"\t."<<it->first<<"="<<it->second<<","<<endl;
    }
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
    string src_path = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c";
    string filename = get_filename(src_path);//提取文件名(无后缀)
    init_code.open("Z:\\computer science\\SAM_DATA\\IP_attical\\gdb_debug_code.c", ios::app|ios::out|ios::in);
    if(!init_code.is_open()){
        cout<<"Error opening file:"<<filename<<endl;
    }
    GDB_script.open("Z:\\computer science\\SAM_DATA\\IP_attical\\gdb_script.gdb",ios::app|ios::out|ios::in);
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
            if(it->second.find("int")!=string::npos){
                GDB_script<<"\tdisplay/d "<<filename<<"1."<<it->first<<endl;
            }else{
                GDB_script<<"\tdisplay/f "<<filename<<"1."<<it->first<<endl;
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

/*计算命题右侧的实际值。例如在命题next(countMode)=countMode+1中,计算countMode+1*/
float64 cal_propos_val(string s, map<string, pair<string, string> > &next, bool flag){//参数为待计算的字符串表达式(即命题右侧部分),flag用于标志当前命题有无next操作符
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){//将命题右侧中的变量替换为当前值
        while(s.find(it->first) != string::npos){
            int val_id = s.find(it->first);
            if(flag==true){//有next操作符
                if(next[it->first].first.length()!=0){
                    s.replace(val_id, it->first.length(), next[it->first].first); 
                } 
                else{
                    s.replace(val_id, it->first.length(), it->second);
                }
            }else{
                s.replace(val_id, it->first.length(), it->second);
            }
        }
    }
    float64 propos_value;
    //调用python处理字符串
    Py_Initialize();
    //判断初始化是否成功
    if(!Py_IsInitialized())
    {
        printf("Python init failed!\n");
        return -1;
    }
    //PyRun_SimpleString("import sys");
    //PyRun_SimpleString("sys.path.append('./')");//若python文件在c++工程下
    // 添加python文件所在的位置
    PyObject* pModule = NULL;
    PyObject* pFunc = NULL;
    PyObject* pArgs = NULL;
	//导入python文件
    pModule = PyImport_ImportModule("fun_cal_string");
    if (!pModule) {
        printf("Can not open python file!\n");
        return -1;
    }
    pFunc = PyObject_GetAttrString(pModule, "cal_string_val");
    PyErr_Print();
    pArgs = PyTuple_New(1);//创建一个元组，长度为1。
	PyTuple_SetItem(pArgs, 0, Py_BuildValue("s", s.c_str()));//将pArgs的第一（0）个变量设置为字符串(s)
    PyObject* pReturn = PyObject_CallObject(pFunc, pArgs);
    PyArg_Parse(pReturn, "d", &propos_value);
    Py_DECREF(pFunc);
    Py_DECREF(pModule);
    Py_Finalize();
    //处理完成
    return propos_value;
}

/*判断etf路径文件的活动属性中命题的正误*/
void judge_proposition(map<string, pair<string, string>> &next, int count, bool last_line){
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){      //定义执行日志中变量值迭代器
        for(int j=0; j<var_exp.size()-1; j++){
            if(var_exp[j].find(it->first)==string::npos) continue;
            string var_exp_id;                                      //从命题中提取变量名
            int op;                                                 //定位命题字符串中比较符的位置                             
            if(var_exp[j].find("next(")!=string::npos){             //命题中存在next操作符
                if(count == 0) continue;
                op = var_exp[j].find(')');                                      
                if(var_exp[j].substr(5, (op-5))==it->first){        //变量名与执行日志中的相同
                    op = op+2;
                    if(var_exp[j][op]=='=') op++;                   //操作符为">=" "<=" "!="
                    float64 re;
                    if(last_line==true){//处理执行路径最后一步中的next操作
                        re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, false);//得到右侧表达式的值
                    }else{
                        re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, true);//得到右侧表达式的值   
                    }
                    if(var_exp[j].find(">=")!=string::npos && stod(it->second)>=re){
                        propos[count-1][j] = true;
                    }else if(var_exp[j].find("<=")!=string::npos && stod(it->second)<=re){
                        propos[count-1][j] = true;
                    }else if(var_exp[j].find("!=")!=string::npos && stod(it->second)!=re){
                        propos[count-1][j] = true;
                    }else if(var_exp[j].find('>')!=string::npos && stod(it->second)>re){
                        propos[count-1][j] = true;
                    }else if(var_exp[j].find('<')!=string::npos && stod(it->second)<re){
                        propos[count-1][j] = true;
                    }else if(var_exp[j].find('=')!=string::npos && stod(it->second)==re){
                        propos[count-1][j] = true;
                    }
                }
            }else if(var_exp[j].find('=')!=string::npos){               //命题中没有next，能够找到“=”比较符
                op = var_exp[j].find('=');
                string temp = var_exp[j];
                float64 re;
                if(temp.find("ADDSUM")!=string::npos){                             //存在累加符(自定义)
                    string s_trans;
                    int st = temp.find("ADDSUM")-1;//只取ADDSUM表达式开始的部分
                    if(temp[op-1]=='<' || temp[op-1]=='>' || temp[op-1]=='!'){
                        s_trans = ADDSUM(temp.substr(st, op-1), var_last_val);
                    }else{
                        s_trans = ADDSUM(temp.substr(st, op), var_last_val);
                    }
                    float64 first = cal_propos_val(s_trans, next, false);
                    op++;
                    re = cal_propos_val(temp.substr(op, var_exp[j].length()-op), next, false);
                    cout<<var_last_val[temp.substr(op, var_exp[j].length()-op)]<<endl;
                    op--;
                    if(temp[op-1]=='!' && first!=re){
                        propos[count][j]=true;
                    }else if(temp[op-1]=='>' && first>=re){
                        propos[count][j]=true;
                    }else if(temp[op-1]=='<' && first<=re){
                        propos[count][j]=true;
                    }else if(temp[op-1]!='<' && temp[op-1]!='>' && temp[op-1]!='!' && first==re){
                        propos[count][j]=true;
                    }
                    continue;
                }
                op++;
                re = cal_propos_val(temp.substr(op, var_exp[j].length()-op), next, false);
                op--;
                if(temp[op-1] == '>'){                                //该运算符为">="
                    var_exp_id = temp.substr(0, (op-1));              //提取命题中的变量名
                    if(var_exp_id==it->first && stod(it->second)>=re){                      //命题变量名与执行日志该行中的变量名相同
                        propos[count][j] = true;
                    }
                }else if(temp[op-1] == '<'){                          //该运算符为"<="
                    var_exp_id = temp.substr(0, (op-1));
                    if(var_exp_id==it->first && stod(it->second)<=re){                      
                        propos[count][j] = true;
                    }
                }else if(temp[op-1] == '!'){                           //运算符为"!="
                    var_exp_id = temp.substr(0, (op-1));
                    if(var_exp_id==it->first && stod(it->second)!=re){                      
                        propos[count][j] = true;
                    }
                }else{                                               //运算符为"="
                    var_exp_id = temp.substr(0, (op));
                    if(var_exp_id==it->first && stod(it->second)==re){                    
                        propos[count][j] = true;
                    }
                } 
            }else if(var_exp[j].find('>')!=string::npos){         //命题中运算符为">"
                op = var_exp[j].find('>');
                op++;
                float64 re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, false);
                op--;
                var_exp_id = var_exp[j].substr(0, op);
                if(it->first==var_exp_id && stod(it->second)>re){
                    propos[count][j] = true;
                }
            }else if(var_exp[j].find('<') != string::npos){         //命题中运算符为"<"
                op = var_exp[j].find('<');
                op++;
                float64 re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, false);
                op--;
                var_exp_id = var_exp[j].substr(0, op);
                if(it->first==var_exp_id && stod(it->second)<re){
                    propos[count][j] = true;
                }
            }     
        }
    }
    return;
}

/*提取执行日志,并转换为etf路径文件*/
void read_trace(int index){

    string line;
    int num_bp = 0;                                   //通过记录执行日志打印的断点数记录生成的路径长度
    bool last_line = false;                           //用于记录是否读到文件末尾，与next操作符关联          
    trace_infile.open((cp_path+"trace"+to_string(index)+".txt").c_str(), ios::app|ios::out|ios::in);
    trace_outfile.open((cp_path+"TRACE"+to_string(index)+".etf").c_str(), ios::app|ios::out|ios::in);
    if (!trace_outfile.is_open())		                        //判断文件是否成功打开
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
            	judge_proposition(next, num_bp, true);
                num_bp++;
            	break;
            } 
            judge_proposition(next, num_bp, last_line);
            num_bp++;
            for(auto it=next.begin(); it!=next.end(); it++){
                if(it->second.second.length() != 0) it->second.first = it->second.second;
            }
        }
                                          
    }
    for(int i=0; i<num_bp; i++){
        trace_outfile<<"C "<<i<<" ";
        trace_outfile<<fixed<<setprecision(1)<<1.0*i<<" "<<1.0*(i+1)<<" 0 100.0;";//输出活动的定义  
        for(int j=0; j<var_exp.size()-1; j++){
            trace_outfile<<boolalpha<<"p"<<j+1<<"="<<propos[i][j];
            if(j<var_exp.size()-2) trace_outfile<<",";
        }
        trace_outfile<<"\n";
    }
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
    KLEE_generate_testcase();
    // 
    // generate_execu_log();
    // generate_GDB_script();
    for(int i=1; i<=12; i++){
        read_test_case(i);
        read_trace(i);
    }
    // time_t ed = clock();
    // cout<<(double)(ed-be)/CLOCKS_PER_SEC<<"s"<<endl;
    return 0;
}