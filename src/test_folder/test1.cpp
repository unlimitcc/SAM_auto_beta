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

map<int, string> var_exp;                                      //��¼��������ȡ���ı������ʽ��Ϊ����
vector<string> var;                                            //�洢��������ȡ���ı���
map<string, string> var_type;                                  //��¼ͷ�ļ��и�������������������

ifstream property_infile;                                      //����֤�����ļ����Թ涨����ʽ��д:extract_var()
fstream var_store_outfile;                                     //�����������ȡ�ı���(�м��ļ�)
ifstream src_code_c;                                           //����IP.cԴ�ļ�
ifstream src_code_h;                                           //����IP.hͷ�ļ�
fstream klee_code;                                             //����KLEE�������ɲ��������Ĵ����ļ�


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
                if(line[i-1]=='-') continue;                       //�����̺��������->�����
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
    property_infile.close();
    var_store_outfile.close();
    return;
}

void KLEE_generate_testcase(){
    src_code_c.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.c");
    src_code_h.open("Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_AttiCal\\Implement\\AttiCal.h");
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
    klee_code.open("Z:\\computer science\\SAM_DATA\\IP_attical\\klee_code.c",ios::app|ios::out|ios::in);
    klee_code<<"#include \"klee/klee.h\"\n"<<"#include <string.h>"<<endl;
    map<string, unint32> array;//��ʶ���飺<���������������һ����ֵ�±�>
    bool branch;            //��ʶ����IPʵ�����Ƿ����������֧
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
    //�����Сȷ��
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

int main(){

    KLEE_generate_testcase();
    for(auto it=var_type.begin(); it!=var_type.end(); it++){
        cout<<it->first<<" "<<it->second<<endl;
    }
}