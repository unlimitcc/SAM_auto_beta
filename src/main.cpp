/*���������ڴ�KLEE���ɵĲ��������ļ�����ȡ�����ֵ�������ݲ�����
������ִ����־��֮��ִ����־ת��Ϊetf·���ļ�*/
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

map<string, string> test_case;                                 //��¼��ȡ���Ĳ�������
map<int, string> var_exp;                                      //��¼��������ȡ���ı������ʽ��Ϊ����
vector<string> var;                                            //�洢��������ȡ���ı���
map<string, string> op;                                        //�洢�����е�ʱ���������TRACE������ʱ���������Ӧ��ϵ(���ʼ��)
map<string, string> execu_log;                                 //��¼ִ����־����ȡ�ı��������ֵ
bool propos[20][101];                                          //��¼TRACE��claim������ֵ
map<string, string> var_last_val;                              //��¼��ǰ�����и�������������ֵ,(��Ҫ��ʼ���Ĺ���)
map<string, string> var_type;                                  //��¼ͷ�ļ��и�������������������

ifstream property_infile;                                      //����֤�����ļ����Թ涨����ʽ��д:extract_var()
fstream var_store_outfile;                                     //�����������ȡ�ı���(�м��ļ�)
fstream TRACE_property;                                        //TRACE���������ļ�
ifstream test_case_infile;                                     //��������Դ�ļ�:read_test_case()        
fstream trace_infile;                                          //GDB���ɵĳ���ִ����־:read_trace()
fstream trace_outfile;                                         //ת�����TRACE·���ļ�
fstream GDB_script;                                            //GDB�Զ����ű�
ifstream src_code_c;                                           //����IP.cԴ�ļ�
ifstream src_code_h;                                           //����IP.hͷ�ļ�
fstream klee_code;                                             //����KLEE�������ɲ��������Ĵ����ļ�
fstream init_code;                                             //ʹ��KLEE���ɵĲ���������ʼ�����IP

/*����д�������ļ�ת��Ϊ����TRACE��ʽ��LTL����*/
void generate_TRACE_property(string name){

    op["&"] = "and";
    op["|"] = "or";
    op["F"] = "finally";
    op["G"] = "globally";
    string s_name = name + "IP_gyrochoose_property.txt";
    string d_name = name + "trace_property.etl";
    property_infile.open(name);
    TRACE_property.open(d_name, ios::app|ios::in|ios::out);
    while(!property_infile.eof()){
        string line;
        getline(property_infile, line);
        for(int i=0; i<var_exp.size()-1; i++){
            while(line.find(var_exp[i])!=string::npos){                                     //��ƥ����ַ���,����������count�Լ�count+1�������г���count+1ʱ���ܳ��ִ���
                int st = line.find(var_exp[i]);
                if((line[st-1]!=' ' && line[st-1]!='(') || (line[st+var_exp[i].length()]!=' ' && line[st+var_exp[i].length()]!=')')) break;
                string pro = "p"+to_string(i+1);
                line.replace(line.find(var_exp[i]), var_exp[i].length(), pro);
            }
        }
        for(auto it=op.begin(); it!=op.end(); it++){
            while(line.find(it->first)!=string::npos){
                line.replace(line.find(it->first), it->first.length(), it->second);
            } 
        }
        TRACE_property<<line<<endl;
    }
    TRACE_property.close();
    return;
}

/*����������ȡ���ɲ���������صı������������ʽ����������KLEE���з��Ż����ɲ������������ʽ����ΪTRACE��������*/
void extract_var(){

    int count_var = 0, count_var_exp = 0;                       //��¼��ȡ�ı���,���������ʽ����
    map<string, int> pro;                                       //��¼������صı��ʽ
    string IP_name = "Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\"; //IP·��
    string filename = IP_name + "IP_gyrochoose_property.txt";         //��������ļ���
    property_infile.open(filename);
    if (!property_infile.is_open())		                           //�ж��ļ��Ƿ�ɹ���
	{
		cout<<"Error opening file:modecontrol_property.txt"<<endl;
	}
    var_store_outfile.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\IP_gyrochoose_propos.txt", ios::app|ios::out|ios::in);
    while(!property_infile.eof()){
        string line, var_id, var_val;
        int begin_var, end_val;
        getline(property_infile, line);
        if(line.length()==0) continue;                             //������ֱ������
        for(int i=0; i<line.length(); i++){                        //��������Ĵ���֤���ʣ���¼���ֹ��ı���
            if(line[i]=='=' || line[i]=='>' || line[i]=='<' || line[i]=='!'){
                if(line[i-1]=='-' && line[i]=='>') continue;                       //�����̺��������->�����
                if(line[i-1]=='>' || line[i-1]=='<' || line[i-1]=='!') continue;     //���������">=""<="���
                /*��ȡ������*/
                int j = i;                                         //j��ʾ"=/>/</!"��λ��
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
                        //if(bal<0) cout<<"�����ļ���ʽ�������"<<endl;
					}else{
						if(line[j-1]=='('){
							break;
						}
						j--;
						var_name.insert(0,1,line[j]);
					}
                }
                if(j<0){
                    cout<<"�����ļ������ʽ����1\n"<<endl; 
                    return;
                }
                //��ȡ������ʱ����next��������������
                begin_var = j;
                if(line.substr(begin_var, (i-begin_var)).find("next") != string::npos){
                    var_id =  line.substr(begin_var+5, (i-begin_var-6));
                }else{
                    var_id = line.substr(begin_var, (i-begin_var));
                }
                if(find(var.begin(), var.end(), var_id) == var.end()) var.push_back(var_id);    //�ظ�������ֻ��¼һ��                                       
                /*��ȡ����ֵ*/
                if(line[i+1]=='='){                                  //����>=��,"<="���
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
                    cout<<"�����ļ������ʽ����2\n"<<endl; 
                    return;
                }
                end_val = k-1;
                var_val = line.substr(j+1, end_val-j);
                string temp = line.substr(begin_var, end_val-begin_var+1);      //������ֵΪ�ַ����͵�ʱ����ν����
                if(pro[temp] != 1){                                             //��ͬ�ı������ʽֻ�洢һ��
                    pro[temp] = 1;
                    var_exp[count_var_exp] = temp;
                    if(var_exp[count_var_exp]<var_exp[count_var_exp-1] && count_var_exp>0){ 
                        for(int k = count_var_exp; k>0; k--){                           //����洢���еı��ʽ�����ں����ж������ֵ
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
    // for(int i=0; i<count_var_exp; i++){                      //����ȡ���������뵽����ļ���(ÿ����ȡ�ı������ʽ��Ӧһ������)
    //     var_store_outfile<<var_exp[i]<<"\n";
    // }
    //generate_TRACE_property(IP_name);
    property_infile.close();
    var_store_outfile.close();
    return;
}

/*���������Ż�������KLEE���ɲ�������*/
void KLEE_generate_testcase(){
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.c");
    src_code_h.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.h");
    map<string, string> symbolic_var;//�����Ż��ı���<����������������> 
    while(!src_code_h.eof()){
        string line;
        getline(src_code_h, line);
        if((line.find("int")!=string::npos || line.find("oat")!=string::npos) && line.find(";")!=string::npos){
            int type_s, type_e;
            if(line.find("int")!=string::npos){//siint��int�ͱ���
                type_s = line.find("int") - 2;//��λ��������
                type_e = line.find("int") + 4;
            }else{//float�ͱ���
                type_s = line.find("oat") - 2;
                type_e = line.find("oat") + 4;
            }
            int var_s = type_e + 2;//��λ������
            while(line[var_s]==' ' || line[var_s]=='\t') var_s++;
            int var_e = line.find(";") - 1;
            var_type[line.substr(var_s, var_e-var_s+1)] = line.substr(type_s, type_e-type_s+1);
        }
    }
    klee_code.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\klee_code.c",ios::app|ios::out|ios::in);
    klee_code<<"#include \"klee/klee.h\"\n"<<"#include <string.h>"<<endl;
    map<string, unint32> array;//��ʶ����<�������������С>
    bool branch;               //��ʶ����IPʵ�����Ƿ����������֧
    while(!src_code_c.eof()){
        string line;
        getline(src_code_c, line);
        klee_code<<line<<endl;
        if(line.find("if")!=string::npos){//��λIP�еķ�֧����(�п��ܲ����ڷ�֧)
            find_symbolic_var(line, var_type, symbolic_var, array);
            branch = true;
        }
    }
    if(branch==false){//IP���޷�֧����
        src_code_c.clear();//����ɨ���ļ���ȡ����
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
    string filename = get_filename("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.c");
    klee_code<<filename<<" "<<filename<<"1={"<<endl;
    klee_code<<"\t.fun="<<filename<<"Fun,"<<endl;
    for(auto it=array.begin(); it!=array.end(); it++){
       klee_code<<"\t."<<it->first<<"=&"<<it->first<<"[0],"<<endl;
    }
    klee_code<<"};\n"<<endl; 
    klee_code<<"int main(){"<<endl;
    int count = 0;//�������������ڷ��Ż�����ʹ��
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
       if(branch==false) klee_code<<"\tklee_assume("<<it->first<<"[0]"<<"!=0);\n"<<endl;        //������������ȫ0�Ĳ�������������ȫ0��������Ҫ���е�������
    }
    klee_code<<"\tIPCALL("<<filename<<"1"<<");"<<endl;
    klee_code<<"}"<<endl;
    src_code_c.close();
    src_code_h.close();
}

/*��ȡ��������ʵ��ֵ�ĺ���*/
void read_test_case(){                               
    test_case.clear();
    int begin_name, end_name;                               //��λ������
    int begin_val, end_val;                                 //��λ����ֵ
    int array_size = 0;                                     //������������飬��¼�����С
    unint32 val;
    string line;                                            //�ļ��е�һ��
    test_case_infile.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\testcase_in.txt");
    if (!test_case_infile.is_open())		                           //�ж��ļ��Ƿ�ɹ���
	{
		cout<<"Error opening file:test_case_in.txt"<<endl;
		return;
	}
    string temp, NAME, VAL;                         //temp������ʱ�洢��һ�е����ݣ����ں�����ѯ;NAME,VAL��¼������������ֵ
    string array_name;
    while(!test_case_infile.eof()){
        getline(test_case_infile, line);                    //��ȡ�ļ��е�������
        begin_name = line.find("name");                     //��λ������������ֵ
        bool val_output;                                    //��¼�Ƿ��Ѿ������val,�������û��"int"�ؼ��ʵ����ݣ�ͨ����������߷����ͱ���
        if(begin_name != string::npos){                     //���������
            begin_name += 7;                                //�ӡ�name������������һ���ַ�����Ϊ7���ַ�(�̶�)
            end_name = line.find("'", begin_name+1);
            NAME = line.substr(begin_name,(end_name-begin_name));
            if(NAME.find('[')!=string::npos){
                array_name = NAME;
            }
            val_output = false;                      
        }
        if(NAME.find('[')!=string::npos && array_size==0){ //��ȡ�����С
            getline(test_case_infile, line);
            if(line.find("size")!=string::npos){
                int op = line.find("size");
                op = op+6;
                string size = line.substr(op, line.length()-op);
                array_size = atoi(size.c_str());
            }
        }
        //���ڳ����������ı������޷����ͣ�����Ҫ��ȡuint��������
        if(var_type[NAME].find("unint")!=string::npos){
            begin_val = line.find("uint");   
        }else{
            begin_val = line.find("int");
            if(line[begin_val-1]=='u') continue;                //��ֹ��λ����uint��
        }                  
        if(begin_val != string::npos){                      //�������ֵ
            begin_val += 6;
            end_val = line.find("\n", begin_val+1);
            VAL = line.substr(begin_val,(end_val-begin_val));
            test_case[NAME] = VAL;
            var_last_val[NAME] = VAL;
            val_output = true;
        }else if(line.find("text:")!=string::npos && val_output==false){ //"text:"��һ����������������ĩ�У��ò������ڴ�����������а�������������ʱ
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

/*ʹ��read_test_case����������ֵ������GDB���Եĳ�ʼ���룬��������ִ����־*/
void generate_execu_log(){
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.c");
    init_code.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\gdb_debug_code.c", ios::app|ios::out|ios::in);
    while(!src_code_c.eof()){     //��IPʵ�ֲ��ֿ�������������ִ����־���ļ���
        string line;
        getline(src_code_c, line);
        init_code<<line<<endl;    
    }
    string filename = get_filename("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.c");//�ļ�����IP���ƣ��ڲ��ṹ������һ��
    map<string, string> var_temp;//��ʱ�����ȡ�Ĳ��������еķ�����������
    int size = 0;//ֻ���ڽṹ���е������ʼ��
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
    init_code<<filename<<" "<<filename<<"1={"<<endl;//�������ɵĲ���������ʼ���ṹ���е����ݣ��ṹ������Ϊ���ļ���1�������硰Fg333saCheck1��
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
    init_code<<"};\n"<<endl;//�ṹ���ʼ�����
    init_code<<"int main(){"<<"\n"<<"\tIPCALL("<<filename<<'1'<<");"<<"\n}"<<endl;//����main����������IP
    src_code_c.close();
    init_code.close();
}

/*������ȡ���ı���ֵ����дGDB�Զ����ű�*/
void generate_GDB_script(){
    string src_path = "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_GyroChoose\\Implement\\GyroChoose.c";
    string filename = get_filename(src_path);//��ȡ�ļ���(�޺�׺)
    init_code.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\gdb_debug_code.c", ios::app|ios::out|ios::in);
    if(!init_code.is_open()){
        cout<<"Error opening file:"<<filename<<endl;
    }
    GDB_script.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\gdb_script.gdb",ios::app|ios::out|ios::in);
    int count_line = 0, count_bp = 0;                         //��¼������������,���õĶϵ���
    GDB_script<<"set logging on trace.txt"<<"\n"<<"b "<<"gdb_debug_code.c:main"<<endl;
    for(int i=0; i<var.size(); i++){
        if(var_type[var[i]].length()>0) GDB_script<<"\tdisplay "<<filename<<"1."<<var[i]<<endl;//��IP��ʼ�ṹ���г��ֵı���ʹ��display�ؼ��ּ��ɣ�δ��IP�ж��壬���������г��ֵ���Ҫ������ӡ
    }
    while(!init_code.eof()){
        string code;
        getline(init_code, code);
        count_line++;
        for(int i=0; i<var.size(); i++){
            if(code.find(var[i])!=string::npos && (code.find('=')!=string::npos || code.find('+')!=string::npos || code.find('-')!=string::npos)){//������д����д�����ȡ���ı���ֵ
                if((code.find('(')<code.find(var[i]) && code.find(';')==string::npos) | code.find('{')!=string::npos) continue;//����Ϊ�����ж���,����Ҫ��ϵ�           
                if(code.find(" .") != string::npos) continue;      //ĳЩ�ṹ�������ʼ���Ĺ���
                count_bp++;
                GDB_script<<"b "<<"gdb_debug_code.c"<<":"<<count_line+1<<"\n"<<"\tcommands "<<count_bp<<endl;
                for(int j=0; j<var.size(); j++){//IP�в����ڳ�ʼ����ı���������ӡ
                    if(var_type[var[j]].length()==0){
                        smatch results;
                        string pattern("\\|[a-zA-Z]+\\|");
                        regex r(pattern);
                        string::const_iterator itb = var[j].begin();//��������������ڷ��������ַ���
                        string::const_iterator ite = var[j].end();
                        if(regex_search(itb,ite,results,r)){
                           GDB_script<<"\tprintf\""<<var[j]<<"=%d\\n\", sizeof("<<var[j].substr(1,var[j].length()-2)<<")/sizeof("<<var[j].substr(1,var[j].length()-2)<<"[0]),"<<endl; 
                        }
                    }
                }
                GDB_script<<"\tcontinue"<<"\n"<<"end"<<endl;
                break;    
            }
        }
        if(code.find('}')==0 && count_bp>0){			//��֤��IPʵ�ַ���ǰ���еı������õ�����
            GDB_script<<"b "<<"gdb_debug_code.c"<<":"<<count_line<<"\n"<<"\tcommands "<<count_bp+1<<endl;
            GDB_script<<"\tcontinue"<<"\n"<<"end"<<endl;
            break;
        }
    }
    GDB_script<<"run"<<endl;
    GDB_script.close();
    src_code_c.close();
    init_code.close();
    //�������ڵ���GDBȥ�����������ɵĳ�ʼ�����IP�������ɳ���ִ����־
    //system("gcc -g gdb_debug_code.c -o gdb_debug_code");
    //system("gdb gdb_debug_code");
    //system("source gdb_script.gdb");  
}

/*���������Ҳ��ʵ��ֵ������������next(countMode)=countMode+1��,����countMode+1*/
float64 cal_propos_val(string s, map<string, pair<string, string> > &next, bool flag){//����Ϊ��������ַ������ʽ(�������Ҳಿ��),flag���ڱ�־��ǰ��������next������
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){//�������Ҳ��еı����滻Ϊ��ǰֵ
        while(s.find(it->first) != string::npos){
            int val_id = s.find(it->first);
            if(flag==true){//��next������
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
    //����python�����ַ���
    Py_Initialize();
    //�жϳ�ʼ���Ƿ�ɹ�
    if(!Py_IsInitialized())
    {
        printf("Python init failed!\n");
        return -1;
    }
    //PyRun_SimpleString("import sys");
    //PyRun_SimpleString("sys.path.append('./')");//��python�ļ���c++������
    // ���python�ļ����ڵ�λ��
    PyObject* pModule = NULL;
    PyObject* pFunc = NULL;
    PyObject* pArgs = NULL;
	//����python�ļ�
    pModule = PyImport_ImportModule("fun_cal_string");
    if (!pModule) {
        printf("Can not open python file!\n");
        return -1;
    }
    pFunc = PyObject_GetAttrString(pModule, "cal_string_val");
    PyErr_Print();
    pArgs = PyTuple_New(1);//����һ��Ԫ�飬����Ϊ1��
	PyTuple_SetItem(pArgs, 0, Py_BuildValue("s", s.c_str()));//��pArgs�ĵ�һ��0������������Ϊ�ַ���(s)
    PyObject* pReturn = PyObject_CallObject(pFunc, pArgs);
    PyArg_Parse(pReturn, "d", &propos_value);
    Py_DECREF(pFunc);
    Py_DECREF(pModule);
    Py_Finalize();
    //�������
    return propos_value;
}

/*�ж�etf·���ļ��Ļ���������������*/
void judge_proposition(map<string, pair<string, string>> &next, int count, bool last_line){
    for(auto it=var_last_val.begin(); it!=var_last_val.end(); it++){      //����ִ����־�б���ֵ������
        for(int j=0; j<var_exp.size()-1; j++){
            if(var_exp[j].find(it->first)==string::npos) continue;
            string var_exp_id;                                      //����������ȡ������
            int op;                                                 //��λ�����ַ����бȽϷ���λ��                             
            if(var_exp[j].find("next(")!=string::npos){             //�����д���next������
                if(count == 0) continue;
                op = var_exp[j].find(')');                                      
                if(var_exp[j].substr(5, (op-5))==it->first){        //��������ִ����־�е���ͬ
                    op = op+2;
                    if(var_exp[j][op]=='=') op++;                   //������Ϊ">=" "<=" "!="
                    float64 re;
                    if(last_line==true){//����ִ��·�����һ���е�next����
                        re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, false);//�õ��Ҳ���ʽ��ֵ
                    }else{
                        re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, true);//�õ��Ҳ���ʽ��ֵ   
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
            }else if(var_exp[j].find('=')!=string::npos){               //������û��next���ܹ��ҵ���=���ȽϷ�
                op = var_exp[j].find('=');
                string temp = var_exp[j];
                float64 re;
                if(temp.find("ADDSUM")!=string::npos){                             //�����ۼӷ�(�Զ���)
                    string s_trans;
                    int st = temp.find("ADDSUM")-1;//ֻȡADDSUM���ʽ��ʼ�Ĳ���
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
                if(temp[op-1] == '>'){                                //�������Ϊ">="
                    var_exp_id = temp.substr(0, (op-1));              //��ȡ�����еı�����
                    if(var_exp_id==it->first && stod(it->second)>=re){                      //�����������ִ����־�����еı�������ͬ
                        propos[count][j] = true;
                    }
                }else if(temp[op-1] == '<'){                          //�������Ϊ"<="
                    var_exp_id = temp.substr(0, (op-1));
                    if(var_exp_id==it->first && stod(it->second)<=re){                      
                        propos[count][j] = true;
                    }
                }else if(temp[op-1] == '!'){                           //�����Ϊ"!="
                    var_exp_id = temp.substr(0, (op-1));
                    if(var_exp_id==it->first && stod(it->second)!=re){                      
                        propos[count][j] = true;
                    }
                }else{                                               //�����Ϊ"="
                    var_exp_id = temp.substr(0, (op));
                    if(var_exp_id==it->first && stod(it->second)==re){                    
                        propos[count][j] = true;
                    }
                } 
            }else if(var_exp[j].find('>')!=string::npos){         //�����������Ϊ">"
                op = var_exp[j].find('>');
                op++;
                float64 re = cal_propos_val(var_exp[j].substr(op, var_exp[j].length()-op), next, false);
                op--;
                var_exp_id = var_exp[j].substr(0, op);
                if(it->first==var_exp_id && stod(it->second)>re){
                    propos[count][j] = true;
                }
            }else if(var_exp[j].find('<') != string::npos){         //�����������Ϊ"<"
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

/*��ȡִ����־,��ת��Ϊetf·���ļ�*/
void read_trace(){

    string line;
    int num_bp = 0;                                   //ͨ����¼ִ����־��ӡ�Ķϵ�����¼���ɵ�·������
    bool last_line = false;                           //���ڼ�¼�Ƿ�����ļ�ĩβ����next����������          
    trace_infile.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\trace.txt", ios::app|ios::out|ios::in);
    trace_outfile.open("Z:\\computer science\\SAM_DATA\\IP_gyrochoose\\TRACE.etf", ios::app|ios::out|ios::in);
    if (!trace_outfile.is_open())		                        //�ж��ļ��Ƿ�ɹ���
	{
		cout<<"Error opening file:trace.txt"<<endl;
	}
    trace_outfile<<"TU MILLISECONDS\n"<<"R 0 100.0 false;\n";
    map<string, pair<string, string>> next;                                  //first��ŵ�ǰ����ֵ��second����¸�״̬����ֵ������֮��Ƚ�
    while( !trace_infile.eof()){              
        getline(trace_infile, line);
        if(line.find("exited") != string::npos){
            judge_proposition(next, num_bp, true);
            break;
        } 
        if((line[0]-'0')<10 && (line[0]-'0')>0 && line.find(':')==string::npos){      //��λ�ϵ��λ�ã����п�ͷΪ������Ϊʶ���ʶ
            string para_name, para_val;                         //�洢������������ֵ
            for(int i=0; i<var.size()+1 && line.length()!=0; i++){
                getline(trace_infile, line);
                if(line.find('=')==string::npos) break;
                int j = line.find("=");
                if(line.find('.')!=string::npos){
                    int aux1;                 //������¼��������λ�ã��Ա��������м򻯣�ȥ�������ڵĽṹ�������(Ҳ���Ը�����Ҫ����)
                    aux1 = line.find('.');
                    para_name = line.substr(aux1+1, j-aux1-2);
                    para_val = line.substr(j+2, line.length()-(j+2));
                }else{
                    int aux2 = line.find(':');
                    para_name = line.substr(aux2+2, j-aux2-3);
                    para_val = line.substr(j+2, line.length()-(j+2));
                }
                var_last_val[para_name] = para_val;                 //ִ����־�����µı���ֵ���� 
                if(next[para_name].first.length()==0){
                    next[para_name].first = para_val;
                }else{
                    next[para_name].second = para_val;
                }
            }
            judge_proposition(next, num_bp, last_line);
            num_bp++;
            for(int i=0; i<var.size(); i++){
                if(next[var[i]].second.length() != 0) next[var[i]].first = next[var[i]].second;
            }
        }                                  
    }
    for(int i=0; i<num_bp; i++){
        trace_outfile<<"C "<<i<<" ";
        trace_outfile<<fixed<<setprecision(1)<<1.0*i<<" "<<1.0*(i+1)<<" 0 100.0;";//�����Ķ���  
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
    var_last_val["false"] = "0";
    var_last_val["true"] = "1";
    var_last_val["^"] = "**";
    //var_last_val["dtime"] = "0.404755";
    //var_last_val["^"] = "**";
    //var_last_val["numOffPeriod"] = "2";
    //var_last_val["numOnPeriod"] = "30";
    //extract_var();
    KLEE_generate_testcase();
    //read_test_case();
    //generate_execu_log();
    //generate_GDB_script();
    //read_trace();
    return 0;
}