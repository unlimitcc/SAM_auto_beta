#include "Z:\\computer science\\VScode\\vscode_project\\IP_verify\\IP_PowerOnJudge\\Implement\\PowerOnJudge.h"
#include <iostream>

using namespace std;

/* IP实体 */
void PowerOnJudgeFun(void *pIp)
{
	PowerOnJudge *p = (PowerOnJudge*)pIp;
	unint32 powerState = p->powerState;

	/* 本周期电源状态为断电 */
	if(powerState == DEV_INVALID)	//DEV_INVALID = 0
	{
		if(p->cntPowerOff < p->numOffPeriod)	//numOffPeriod初始化为2
		{
			p->cntPowerOff++;
		}
		else
		{
			/* 已断电 */
			p->cntPowerOn = 0;
			p->powerPr1 = DEV_INVALID;
			p->bPowerOnOk = FALSE32; 
		}
	}
	else if((p->powerPr1 == DEV_INVALID) && (powerState == DEV_POWERON))  /* 电源状态由断电变加电, DEV_POWERON = 255(0xFF) */
	{
		p->cntPowerOn++;

		if(p->cntPowerOn > p->numOnPeriod)	//numOnPeriod初始化为30
		{
			p->cntPowerOff = 0;
			/* 认为已加电大于30s */
			p->bPowerOnOk = TRUE32;
		}
		else
		{
			/* 加电不足30s,延续上一周期的电源状态 */
			powerState = DEV_INVALID;
		}
	}
	else
	{
		/* 电源状态没有发生变化 */
		NULL_STATEMENT();
	}
	/* 保存本周期电源状态 */
	p->powerPr1 = powerState;
	return;
}

PowerOnJudge PowerOnJudge1={
	.fun=PowerOnJudgeFun,
	.powerState=255,
	.powerPr1=0,
	.cntPowerOn=0,
	.cntPowerOff=0,
	.numOnPeriod=30,
	.numOffPeriod=2,
};

int main(){
	IPCALL(PowerOnJudge1);
	//cout<<PowerOnJudge1.powerState<<endl;
	//cout<<PowerOnJudge1.cntPowerOn<<endl;
}
