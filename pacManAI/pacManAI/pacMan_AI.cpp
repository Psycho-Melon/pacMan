#include <fstream>
#include <cstdio>
#include <cstdlib>
#include <ctime>
#include <iostream>
#include <algorithm>
#include <string>
#include <cstring>
#include <stack>
#include <stdexcept>
#include <string.h>
#include "jsoncpp/json.h"
#include <time.h>
#include <stdio.h>

#define CHAR_START 65
#define FIELD_MAX_HEIGHT 12
#define FIELD_MAX_WIDTH 12
#define MAX_GENERATOR_COUNT 4 // 每个象限1
#define MAX_PLAYER_COUNT 4
#define MAX_TURN 100


// 你也可以选用 using namespace std; 但是会污染命名空间
using std::string;
using std::swap;
using std::cin;
using std::cout;
using std::endl;
using std::getline;
using std::runtime_error;
using std::memcpy;

string test = "test";
char disBetween[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH]
[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH]; // 两点间距离加一(便于判断是否计算过)加CHAR_START
char save_steps[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//最终得到的记录

// 平台提供的吃豆人相关逻辑处理程序
namespace Pacman
{
	const time_t seed = time(0);
	const int dx[] = { 0, 1, 0, -1, 1, 1, -1, -1 }, dy[] = { -1, 0, 1, 0, -1, 1, 1, -1 };

	// 枚举定义；使用枚举虽然会浪费空间（sizeof(GridContentType) == 4），但是计算机处理32位的数字效率更高

	// 每个格子可能变化的内容，会采用“或”逻辑进行组合
	enum GridContentType
	{
		empty = 0, // 其实不会用到
		player1 = 1, // 1号玩家
		player2 = 2, // 2号玩家
		player3 = 4, // 3号玩家
		player4 = 8, // 4号玩家
		playerMask = 1 | 2 | 4 | 8, // 用于检查有没有玩家等
		smallFruit = 16, // 小豆子
		largeFruit = 32 // 大豆子
	};

	// 用玩家ID换取格子上玩家的二进制位
	GridContentType playerID2Mask[] = { player1, player2, player3, player4 };
	string playerID2str[] = { "0", "1", "2", "3" };

	// 让枚举也可以用这些运算了（不加会编译错误）
	template<typename T>
	inline T operator |=(T &a, const T &b)
	{
		return a = static_cast<T>(static_cast<int>(a) | static_cast<int>(b));
	}
	template<typename T>
	inline T operator |(const T &a, const T &b)
	{
		return static_cast<T>(static_cast<int>(a) | static_cast<int>(b));
	}
	template<typename T>
	inline T operator &=(T &a, const T &b)
	{
		return a = static_cast<T>(static_cast<int>(a) & static_cast<int>(b));
	}
	template<typename T>
	inline T operator &(const T &a, const T &b)
	{
		return static_cast<T>(static_cast<int>(a) & static_cast<int>(b));
	}
	template<typename T>
	inline T operator ++(T &a)
	{
		return a = static_cast<T>(static_cast<int>(a) + 1);
	}
	template<typename T>
	inline T operator ~(const T &a)
	{
		return static_cast<T>(~static_cast<int>(a));
	}

	// 每个格子固定的东西，会采用“或”逻辑进行组合
	enum GridStaticType
	{
		emptyWall = 0, // 其实不会用到
		wallNorth = 1, // 北墙（纵坐标减少的方向）
		wallEast = 2, // 东墙（横坐标增加的方向）
		wallSouth = 4, // 南墙（纵坐标增加的方向）
		wallWest = 8, // 西墙（横坐标减少的方向）
		generator = 16 // 豆子产生器
	};

	// 用移动方向换取这个方向上阻挡着的墙的二进制位
	GridStaticType direction2OpposingWall[] = { wallNorth, wallEast, wallSouth, wallWest };

	// 方向，可以代入dx、dy数组，同时也可以作为玩家的动作
	enum Direction
	{
		stay = -1,
		up = 0,
		right = 1,
		down = 2,
		left = 3,
		// 下面的这几个只是为了产生器程序方便，不会实际用到
		ur = 4, // 右上
		dr = 5, // 右下
		dl = 6, // 左下
		ul = 7 // 左上
	};

	// 场地上带有坐标的物件
	struct FieldProp
	{
		int row, col;
	};

	// 场地上的玩家
	struct Player : FieldProp
	{
		int strength;
		int powerUpLeft;
		bool dead;
	};

	// 回合新产生的豆子的坐标
	struct NewFruits
	{
		FieldProp newFruits[MAX_GENERATOR_COUNT * 8];
		int newFruitCount;
	} newFruits[MAX_TURN];
	int newFruitsCount = 0;

	// 状态转移记录结构
	struct TurnStateTransfer
	{
		enum StatusChange // 可组合
		{
			none = 0,
			ateSmall = 1,
			ateLarge = 2,
			powerUpCancel = 4,
			die = 8,
			error = 16
		};

		// 玩家选定的动作
		Direction actions[MAX_PLAYER_COUNT];

		// 此回合该玩家的状态变化
		StatusChange change[MAX_PLAYER_COUNT];

		// 此回合该玩家的力量变化
		int strengthDelta[MAX_PLAYER_COUNT];
	};

	// 游戏主要逻辑处理类，包括输入输出、回合演算、状态转移，全局唯一
	class GameField
	{
	private:
		// 为了方便，大多数属性都不是private的

		// 记录每回合的变化（栈）
		TurnStateTransfer backtrack[MAX_TURN];

		// 这个对象是否已经创建
		static bool constructed;

	public:
		// 场地的长和宽
		int height, width;
		int generatorCount;
		int GENERATOR_INTERVAL, LARGE_FRUIT_DURATION, LARGE_FRUIT_ENHANCEMENT;

		// 场地格子固定的内容
		GridStaticType fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];

		// 场地格子会变化的内容
		GridContentType fieldContent[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];
		int generatorTurnLeft; // 多少回合后产生豆子
		int aliveCount; // 有多少玩家存活
		int smallFruitCount;
		int turnID;
		FieldProp generators[MAX_GENERATOR_COUNT]; // 有哪些豆子产生器
		Player players[MAX_PLAYER_COUNT]; // 有哪些玩家

										  // 玩家选定的动作
		Direction actions[MAX_PLAYER_COUNT];

		// 恢复到上次场地状态。可以一路恢复到最开始。
		// 恢复失败（没有状态可恢复）返回false
		bool PopState()
		{
			if (turnID <= 0)
				return false;

			const TurnStateTransfer &bt = backtrack[--turnID];
			int i, _;

			// 倒着来恢复状态

			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				GridContentType &content = fieldContent[_p.row][_p.col];
				TurnStateTransfer::StatusChange change = bt.change[_];

				if (!_p.dead)
				{
					// 5. 大豆回合恢复
					if (_p.powerUpLeft || change & TurnStateTransfer::powerUpCancel)
						_p.powerUpLeft++;

					// 4. 吐出豆子
					if (change & TurnStateTransfer::ateSmall)
					{
						content |= smallFruit;
						smallFruitCount++;
					}
					else if (change & TurnStateTransfer::ateLarge)
					{
						content |= largeFruit;
						_p.powerUpLeft -= LARGE_FRUIT_DURATION;
					}
				}

				// 2. 魂兮归来
				if (change & TurnStateTransfer::die)
				{
					_p.dead = false;
					aliveCount++;
					content |= playerID2Mask[_];
				}

				// 1. 移形换影
				if (!_p.dead && bt.actions[_] != stay)
				{
					fieldContent[_p.row][_p.col] &= ~playerID2Mask[_];
					_p.row = (_p.row - dy[bt.actions[_]] + height) % height;
					_p.col = (_p.col - dx[bt.actions[_]] + width) % width;
					fieldContent[_p.row][_p.col] |= playerID2Mask[_];
				}

				// 0. 救赎不合法的灵魂
				if (change & TurnStateTransfer::error)
				{
					_p.dead = false;
					aliveCount++;
					content |= playerID2Mask[_];
				}

				// *. 恢复力量
				if (!_p.dead)
					_p.strength -= bt.strengthDelta[_];
			}

			// 3. 收回豆子
			if (generatorTurnLeft == GENERATOR_INTERVAL)
			{
				generatorTurnLeft = 1;
				NewFruits &fruits = newFruits[--newFruitsCount];
				for (i = 0; i < fruits.newFruitCount; i++)
				{
					fieldContent[fruits.newFruits[i].row][fruits.newFruits[i].col] &= ~smallFruit;
					smallFruitCount--;
				}
			}
			else
				generatorTurnLeft++;

			return true;
		}

		// 判断指定玩家向指定方向移动是不是合法的（没有撞墙）
		inline bool ActionValid(int playerID, Direction &dir) const
		{
			if (dir == stay)
				return true;
			const Player &p = players[playerID];
			const GridStaticType &s = fieldStatic[p.row][p.col];
			return dir >= -1 && dir < 4 && !(s & direction2OpposingWall[dir]);
		}

		// 在向actions写入玩家动作后，演算下一回合局面，并记录之前所有的场地状态，可供日后恢复。
		// 是终局的话就返回false
		bool NextTurn()
		{
			int _, i, j;

			TurnStateTransfer &bt = backtrack[turnID];
			memset(&bt, 0, sizeof(bt));

			// 0. 杀死不合法输入
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &p = players[_];
				if (!p.dead)
				{
					Direction &action = actions[_];
					if (action == stay)
						continue;

					if (!ActionValid(_, action))
					{
						bt.strengthDelta[_] += -p.strength;
						bt.change[_] = TurnStateTransfer::error;
						fieldContent[p.row][p.col] &= ~playerID2Mask[_];
						p.strength = 0;
						p.dead = true;
						aliveCount--;
					}
					else
					{
						// 遇到比自己强♂壮的玩家是不能前进的
						GridContentType target = fieldContent
							[(p.row + dy[action] + height) % height]
						[(p.col + dx[action] + width) % width];
						if (target & playerMask)
							for (i = 0; i < MAX_PLAYER_COUNT; i++)
								if (target & playerID2Mask[i] && players[i].strength > p.strength)
									action = stay;
					}
				}
			}

			// 1. 位置变化
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				bt.actions[_] = actions[_];

				if (actions[_] == stay)
					continue;

				// 移动
				fieldContent[_p.row][_p.col] &= ~playerID2Mask[_];
				_p.row = (_p.row + dy[actions[_]] + height) % height;
				_p.col = (_p.col + dx[actions[_]] + width) % width;
				fieldContent[_p.row][_p.col] |= playerID2Mask[_];
			}

			// 2. 玩家互殴
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				// 判断是否有玩家在一起
				int player, containedCount = 0;
				int containedPlayers[MAX_PLAYER_COUNT];
				for (player = 0; player < MAX_PLAYER_COUNT; player++)
					if (fieldContent[_p.row][_p.col] & playerID2Mask[player])
						containedPlayers[containedCount++] = player;

				if (containedCount > 1)
				{
					// NAIVE
					for (i = 0; i < containedCount; i++)
						for (j = 0; j < containedCount - i - 1; j++)
							if (players[containedPlayers[j]].strength < players[containedPlayers[j + 1]].strength)
								swap(containedPlayers[j], containedPlayers[j + 1]);

					int begin;
					for (begin = 1; begin < containedCount; begin++)
						if (players[containedPlayers[begin - 1]].strength > players[containedPlayers[begin]].strength)
							break;

					// 这些玩家将会被杀死
					int lootedStrength = 0;
					for (i = begin; i < containedCount; i++)
					{
						int id = containedPlayers[i];
						Player &p = players[id];

						// 从格子上移走
						fieldContent[p.row][p.col] &= ~playerID2Mask[id];
						p.dead = true;
						int drop = p.strength / 2;
						bt.strengthDelta[id] += -drop;
						bt.change[id] |= TurnStateTransfer::die;
						lootedStrength += drop;
						p.strength -= drop;
						aliveCount--;
					}

					// 分配给其他玩家
					int inc = lootedStrength / begin;
					for (i = 0; i < begin; i++)
					{
						int id = containedPlayers[i];
						Player &p = players[id];
						bt.strengthDelta[id] += inc;
						p.strength += inc;
					}
				}
			}

			// 3. 产生豆子
			if (--generatorTurnLeft == 0)
			{
				generatorTurnLeft = GENERATOR_INTERVAL;
				NewFruits &fruits = newFruits[newFruitsCount++];
				fruits.newFruitCount = 0;
				for (i = 0; i < generatorCount; i++)
					for (Direction d = up; d < 8; ++d)
					{
						// 取余，穿过场地边界
						int r = (generators[i].row + dy[d] + height) % height, c = (generators[i].col + dx[d] + width) % width;
						if (fieldStatic[r][c] & generator || fieldContent[r][c] & (smallFruit | largeFruit))
							continue;
						fieldContent[r][c] |= smallFruit;
						fruits.newFruits[fruits.newFruitCount].row = r;
						fruits.newFruits[fruits.newFruitCount++].col = c;
						smallFruitCount++;
					}
			}

			// 4. 吃掉豆子
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				GridContentType &content = fieldContent[_p.row][_p.col];

				// 只有在格子上只有自己的时候才能吃掉豆子
				if (content & playerMask & ~playerID2Mask[_])
					continue;

				if (content & smallFruit)
				{
					content &= ~smallFruit;
					_p.strength++;
					bt.strengthDelta[_]++;
					smallFruitCount--;
					bt.change[_] |= TurnStateTransfer::ateSmall;
				}
				else if (content & largeFruit)
				{
					content &= ~largeFruit;
					if (_p.powerUpLeft == 0)
					{
						_p.strength += LARGE_FRUIT_ENHANCEMENT;
						bt.strengthDelta[_] += LARGE_FRUIT_ENHANCEMENT;
					}
					_p.powerUpLeft += LARGE_FRUIT_DURATION;
					bt.change[_] |= TurnStateTransfer::ateLarge;
				}
			}

			// 5. 大豆回合减少
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				if (_p.powerUpLeft > 0 && --_p.powerUpLeft == 0)
				{
					_p.strength -= LARGE_FRUIT_ENHANCEMENT;
					bt.change[_] |= TurnStateTransfer::powerUpCancel;
					bt.strengthDelta[_] += -LARGE_FRUIT_ENHANCEMENT;
				}
			}

			++turnID;

			// 是否只剩一人？
			if (aliveCount <= 1)
			{
				for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
					if (!players[_].dead)
					{
						bt.strengthDelta[_] += smallFruitCount;
						players[_].strength += smallFruitCount;
					}
				return false;
			}

			// 是否回合超限？
			if (turnID >= 100)
				return false;

			return true;
		}

		// 读取并解析程序输入，本地调试或提交平台使用都可以。
		// 如果在本地调试，程序会先试着读取参数中指定的文件作为输入文件，失败后再选择等待用户直接输入。
		// 本地调试时可以接受多行以便操作，Windows下可以用 Ctrl-Z 或一个【空行+回车】表示输入结束，但是在线评测只需接受单行即可。
		// localFileName 可以为NULL
		// obtainedData 会输出自己上回合存储供本回合使用的数据
		// obtainedGlobalData 会输出自己的 Bot 上以前存储的数据
		// 返回值是自己的 playerID
		int ReadInput(const char *localFileName, string &obtainedData, string &obtainedGlobalData)
		{
			string str, chunk;
#ifdef _BOTZONE_ONLINE
			std::ios::sync_with_stdio(false); //ω\\)
			getline(cin, str);
#else
			if (localFileName)
			{
				std::ifstream fin(localFileName,std::ios::binary);
				if (fin)
					while (getline(fin, chunk) && chunk != "")
						str += chunk;
				else
					while (getline(cin, chunk) && chunk != "")
						str += chunk;
			}
			else
				while (getline(cin, chunk) && chunk != "")
					str += chunk;
#endif
			Json::Reader reader;
			Json::Value input;
			reader.parse(str, input);

			int len = input["requests"].size();

			// 读取场地静态状况
			Json::Value field = input["requests"][(Json::Value::UInt) 0],
				staticField = field["static"], // 墙面和产生器
				contentField = field["content"]; // 豆子和玩家
			height = field["height"].asInt();
			width = field["width"].asInt();
			LARGE_FRUIT_DURATION = field["LARGE_FRUIT_DURATION"].asInt();
			LARGE_FRUIT_ENHANCEMENT = field["LARGE_FRUIT_ENHANCEMENT"].asInt();
			generatorTurnLeft = GENERATOR_INTERVAL = field["GENERATOR_INTERVAL"].asInt();

			PrepareInitialField(staticField, contentField);

			// 根据历史恢复局面
			for (int i = 1; i < len; i++)
			{
				Json::Value req = input["requests"][i];
				for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
					if (!players[_].dead)
						actions[_] = (Direction)req[playerID2str[_]]["action"].asInt();
				NextTurn();
			}

			obtainedData = input["data"].asString();
			obtainedGlobalData = input["globaldata"].asString();

			return field["id"].asInt();
		}

		// 根据 static 和 content 数组准备场地的初始状况
		void PrepareInitialField(const Json::Value &staticField, const Json::Value &contentField)
		{
			int r, c, gid = 0;
			generatorCount = 0;
			aliveCount = 0;
			smallFruitCount = 0;
			generatorTurnLeft = GENERATOR_INTERVAL;
			for (r = 0; r < height; r++)
				for (c = 0; c < width; c++)
				{
					GridContentType &content = fieldContent[r][c] = (GridContentType)contentField[r][c].asInt();
					GridStaticType &s = fieldStatic[r][c] = (GridStaticType)staticField[r][c].asInt();
					if (s & generator)
					{
						generators[gid].row = r;
						generators[gid++].col = c;
						generatorCount++;
					}
					if (content & smallFruit)
						smallFruitCount++;
					for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
						if (content & playerID2Mask[_])
						{
							Player &p = players[_];
							p.col = c;
							p.row = r;
							p.powerUpLeft = 0;
							p.strength = 1;
							p.dead = false;
							aliveCount++;
						}
				}
		}

		// 完成决策，输出结果。
		// action 表示本回合的移动方向，stay 为不移动
		// tauntText 表示想要叫嚣的言语，可以是任意字符串，除了显示在屏幕上不会有任何作用，留空表示不叫嚣
		// data 表示自己想存储供下一回合使用的数据，留空表示删除
		// globalData 表示自己想存储供以后使用的数据（替换），这个数据可以跨对局使用，会一直绑定在这个 Bot 上，留空表示删除
		void WriteOutput(Direction action, string tauntText = "", string data = "", string globalData = "") const
		{
			Json::Value ret;
			ret["response"]["action"] = action;
			ret["response"]["tauntText"] = tauntText;
			ret["data"] = data;
			ret["globaldata"] = globalData;
			ret["debug"] = (Json::Int)seed;

#ifdef _BOTZONE_ONLINE
			Json::FastWriter writer; // 在线评测的话能用就行……
#else
			Json::StyledWriter writer; // 本地调试这样好看 > <
#endif
			cout << writer.write(ret) << endl;
		}

		// 用于显示当前游戏状态，调试用。
		// 提交到平台后会被优化掉。
		inline void DebugPrint() const
		{
#ifndef _BOTZONE_ONLINE
			printf("回合号【%d】存活人数【%d】| 图例 产生器[G] 有玩家[0/1/2/3] 多个玩家[*] 大豆[o] 小豆[.]\n", turnID, aliveCount);
			for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				const Player &p = players[_];
				printf("[玩家%d(%d, %d)|力量%d|加成剩余回合%d|%s]\n",
					_, p.row, p.col, p.strength, p.powerUpLeft, p.dead ? "死亡" : "存活");
			}
			putchar(' ');
			putchar(' ');
			for (int c = 0; c < width; c++)
				printf("  %d ", c);
			putchar('\n');
			for (int r = 0; r < height; r++)
			{
				putchar(' ');
				putchar(' ');
				for (int c = 0; c < width; c++)
				{
					putchar(' ');
					printf((fieldStatic[r][c] & wallNorth) ? "---" : "   ");
				}
				printf("\n%d ", r);
				for (int c = 0; c < width; c++)
				{
					putchar((fieldStatic[r][c] & wallWest) ? '|' : ' ');
					putchar(' ');
					int hasPlayer = -1;
					for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
						if (fieldContent[r][c] & playerID2Mask[_])
							if (hasPlayer == -1)
								hasPlayer = _;
							else
								hasPlayer = 4;
					if (hasPlayer == 4)
						putchar('*');
					else if (hasPlayer != -1)
						putchar('0' + hasPlayer);
					else if (fieldStatic[r][c] & generator)
						putchar('G');
					else if (fieldContent[r][c] & playerMask)
						putchar('*');
					else if (fieldContent[r][c] & smallFruit)
						putchar('.');
					else if (fieldContent[r][c] & largeFruit)
						putchar('o');
					else
						putchar(' ');
					putchar(' ');
				}
				putchar((fieldStatic[r][width - 1] & wallEast) ? '|' : ' ');
				putchar('\n');
			}
			putchar(' ');
			putchar(' ');
			for (int c = 0; c < width; c++)
			{
				putchar(' ');
				printf((fieldStatic[height - 1][c] & wallSouth) ? "---" : "   ");
			}
			putchar('\n');
#endif
		}

		Json::Value SerializeCurrentTurnChange()
		{
			Json::Value result;
			TurnStateTransfer &bt = backtrack[turnID - 1];
			for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				result["actions"][_] = bt.actions[_];
				result["strengthDelta"][_] = bt.strengthDelta[_];
				result["change"][_] = bt.change[_];
			}
			return result;
		}

		// 初始化游戏管理器
		GameField()
		{
			if (constructed)
				throw runtime_error("请不要再创建 GameField 对象了，整个程序中只应该有一个对象");
			constructed = true;

			turnID = 0;
		}

		GameField(const GameField &b) : GameField() { }
	};

	bool GameField::constructed = false;
}

// 一些辅助程序
namespace Helpers
{

	int actionScore[5] = {};

	inline int RandBetween(int a, int b)
	{
		if (a > b)
			swap(a, b);
		return rand() % (b - a) + a;
	}

	void RandomPlay(Pacman::GameField &gameField, int myID)
	{
		int count = 0, myAct = -1;
		while (true)
		{
			// 对每个玩家生成随机的合法动作
			for (int i = 0; i < MAX_PLAYER_COUNT; i++)
			{
				if (gameField.players[i].dead)
					continue;
				Pacman::Direction valid[5];
				int vCount = 0;
				for (Pacman::Direction d = Pacman::stay; d < 4; ++d)
					if (gameField.ActionValid(i, d))
						valid[vCount++] = d;
				gameField.actions[i] = valid[RandBetween(0, vCount)];
			}

			if (count == 0)
				myAct = gameField.actions[myID];

			// 演算一步局面变化
			// NextTurn返回true表示游戏没有结束
			bool hasNext = gameField.NextTurn();
			count++;

			if (!hasNext)
				break;
		}

		// 计算分数
		int rank2player[] = { 0, 1, 2, 3 };
		for (int j = 0; j < MAX_PLAYER_COUNT; j++)
			for (int k = 0; k < MAX_PLAYER_COUNT - j - 1; k++)
				if (gameField.players[rank2player[k]].strength > gameField.players[rank2player[k + 1]].strength)
					swap(rank2player[k], rank2player[k + 1]);

		int scorebase = 1;
		if (rank2player[0] == myID)
			actionScore[myAct + 1]++;
		else
			for (int j = 1; j < MAX_PLAYER_COUNT; j++)
			{
				if (gameField.players[rank2player[j - 1]].strength < gameField.players[rank2player[j]].strength)
					scorebase = j + 1;
				if (rank2player[j] == myID)
				{
					actionScore[myAct + 1] += scorebase;
					break;
				}
			}

		// 恢复游戏状态到最初（就是本回合）
		while (count-- > 0)
			gameField.PopState();
	}
}

// Phycho-Melon AI
// started at 2016-5-1

#define MAX_SEARCH_DEPTH 1 // 定义最大搜索步数
#define MAX_DISTANCE 20 // 记录的最大距离
#define DISTANCE_TO_IGNORE_ENEMY 20 // 与敌人距离超过多少则忽略敌人的影响

namespace Value {
	using namespace Pacman;
	// Distance

	int height, width;
	GridContentType fieldContent[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];
	GridStaticType fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];

											 // 每回合开始需要调用一次
	void Initialate(GameField &gameField) {
		height = gameField.height;
		width = gameField.width;
		memcpy(fieldContent, gameField.fieldContent, sizeof(gameField.fieldContent));
		memcpy(fieldStatic, gameField.fieldStatic, sizeof(gameField.fieldStatic));
		memset(disBetween, CHAR_START, sizeof(disBetween));
		//find_dead_end(gameField);
	}
	// 设置某点周围距离辐射
	void SetDis(char(*p)[FIELD_MAX_WIDTH], int dis) {
		for (int i = 0; i < height; i++)
			for (int j = 0; j < width; j++) {
				if (p[i][j] == CHAR_START + dis) {
					GridStaticType &s = fieldStatic[i][j];
					for (Direction dir = up; dir < 4; ++dir) {
						if (!(s&direction2OpposingWall[dir])) {
							char &_p = p[(i + dy[dir] + height) % height][(j + dx[dir] + width) % width];
							if (_p == CHAR_START || _p > CHAR_START + dis)
								_p = CHAR_START + dis + 1;
						}
					}
				}
			}
		if (dis + 1 >= MAX_DISTANCE)return;
		SetDis(p, dis + 1);
	}

	// 记录距离
	void RecordDisBetween(int row1, int col1, int row2, int col2, int dis) {
		disBetween[row1][col1][row2][col2] = CHAR_START + dis;
		disBetween[row2][col2][row1][col1] = CHAR_START + dis;
		disBetween[height - row1][col1][height - row2][col2] = CHAR_START + dis;
		disBetween[height - row2][col2][height - row1][col1] = CHAR_START + dis;
		disBetween[row1][width - col1][row2][width - col2] = CHAR_START + dis;
		disBetween[row2][width - col2][row1][width - col1] = CHAR_START + dis;
		disBetween[height - row1][width - col1][height - row2][width - col2] = CHAR_START + dis;
		disBetween[height - row2][width - col2][height - row1][width - col1] = CHAR_START + dis;
	}

	// 返回两点间距离，-1表示超出计算范围
	int GetDisBetween(int row1, int col1, int row2, int col2) {
		char(*p1)[FIELD_MAX_WIDTH] = disBetween[row1][col1];
		char(*p2)[FIELD_MAX_WIDTH] = disBetween[row2][col2];
		if (p1[row1][col1] == CHAR_START) { // 该点还未计算过
			p1[row1][col1] ++;
			SetDis(p1, 1);
		}

		if (p2[row2][col2] == CHAR_START) {
			p2[row2][col2] ++;
			SetDis(p2, 1);
		}

		// 两点间距离已记录过
		if (p1[row2][col2] > CHAR_START)
			return p1[row2][col2] - CHAR_START - 1;
		// 两点间距离未记录过
		int minDis = 201;
		for (int i = 0; i < height; i++)
			for (int j = 0; j < width; j++) {
				if (p1[i][j]>CHAR_START && p2[i][j]>CHAR_START) {
					int tmp = p1[i][j] + p2[i][j] - 2 * CHAR_START;
					if (tmp < minDis)
						minDis = tmp;
				}
			}
		if (minDis < 201) {
			int tmp = minDis - 1;
			RecordDisBetween(row1, col1, row2, col2, tmp);
			return tmp - 1;
		}
		else
			return -1; // 超出计算范围
	}

	const int valueOfDistance[50] = { 65536,16384,8192,4096,2048,1024,512,256,128,64,32,16,8,4,2,1,0 };

	int GetValue(GameField &gameField, int myID) {
		int value = 0;
		Player &p = gameField.players[myID];

		// 记录存活敌人,以及与其距离
		Player enemy[3];
		int disToEnemy[3];
		int enemyCount = 0;
		for (int i = 0; i < 4; ++i) {
			if (i != myID&&gameField.players[i].dead == false) {
				enemy[enemyCount] = gameField.players[i];
				disToEnemy[enemyCount] = GetDisBetween(p.row, p.col, enemy[enemyCount].row, enemy[enemyCount].col);
				if (0<disToEnemy[enemyCount]&&disToEnemy[enemyCount]<=DISTANCE_TO_IGNORE_ENEMY) // 与敌人距离太远或重叠则直接忽略
					enemyCount++;
			}
		}

		// 吃豆估值
		for (int i = 0; i < height; ++i) {
			for (int j = 0; j < width; ++j) {
				if (gameField.fieldContent[i][j] & smallFruit) {
					int dis = GetDisBetween(p.row, p.col, i, j);
					if (dis >= 0) {
						int disRivise = 0; // 距离修正
						bool enemyInPath = false;
						for (int k = 0; k < enemyCount; ++k) {
							int enemyToFruit = GetDisBetween(enemy[k].row, enemy[k].col, i, j);							
							if (enemyToFruit >= 0 && enemyToFruit < dis) { // 敌人离豆子更近,降低该豆估值
								if (disToEnemy[k] > 0 && disToEnemy[k] + enemyToFruit == dis) { // 敌人在自己前方
									disRivise ++;
									//enemyInPath = true;
									//break;
								}
							}
							disRivise++;
						}
						if (enemyInPath)
							continue;
						value += valueOfDistance[dis + disRivise];
					}					
				}
			}
		}
		return value;
	}
	
	//记录死胡同——————————————————————————————————————————————

	void find_dead_end(Pacman::GameField & gameField)
	{
		int Height = gameField.height, Width = gameField.width;
		int tmp_I = Height / 2 + Height % 2, tmp_J = Width / 2 + Width % 2;

		int save_dead_ends[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//标记胡同及入口
		int tmp_fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//记录地图信息并做标记

		for (int i = 0; i < FIELD_MAX_HEIGHT; i++)
		{
			for (int j = 0; j < FIELD_MAX_WIDTH; j++)
			{
				save_dead_ends[i][j] = 0;
				save_steps[i][j] = CHAR_START;
			}
		}//初始化
		for (int i = 0; i < Height; i++)
			for (int j = 0; j < Width; j++) tmp_fieldStatic[i][j] = gameField.fieldStatic[i][j];
		//从gamefield读取地图信息

		int flag = 1, counter = 0;
		while (flag == 1)
		{
			flag = 0;
			for (int i = 0; i < tmp_I; i++)
			{
				for (int j = 0; j < tmp_J; j++)
				{
					counter = 0;
					if (tmp_fieldStatic[i][j] & 1)counter++;
					if (tmp_fieldStatic[i][j] & 2) counter++;
					if (tmp_fieldStatic[i][j] & 4) counter++;
					if (tmp_fieldStatic[i][j] & 8) counter++;
					if (counter == 3)
					{
						flag = 1;
						int lost_wall = 15 - tmp_fieldStatic[i][j];
						save_dead_ends[i][j] = 1;
						tmp_fieldStatic[i][j] = 15;
						if (lost_wall == 1) {
							save_dead_ends[i - 1][j] = save_dead_ends[i][j] - 2;
							tmp_fieldStatic[i - 1][j] += 4;
						}
						else if (lost_wall == 2) {
							save_dead_ends[i][j + 1] = save_dead_ends[i][j] - 2;
							tmp_fieldStatic[i][j + 1] += 8;
						}
						else if (lost_wall == 4) {
							save_dead_ends[i + 1][j] = save_dead_ends[i][j] - 2;
							tmp_fieldStatic[i + 1][j] += 1;
						}
						else if (lost_wall == 8) {
							save_dead_ends[i][j - 1] = save_dead_ends[i][j] - 2;
							tmp_fieldStatic[i][j - 1] += 2;
						}
					}
				}
			}
		}//第一次，找出胡同并做标记，记录在save_dead_end上
		 /*
		 save_dead_end数据类型（int）
		 0：不在胡同且一步走不到胡同
		 -1：一步有可能走到胡同
		 1：hutong*/

		counter = 1; flag = 1;//counter记录胡同深度
		while (flag)
		{
			flag = 0;
			for (int i = 0; i < tmp_I; i++)
			{
				for (int j = 0; j < tmp_J; j++)
				{
					if (save_dead_ends[i][j] == -1)
					{
						if (i > 0 && save_dead_ends[i - 1][j] == 1) { save_steps[i - 1][j] += counter; save_dead_ends[i - 1][j] = -2; flag = 1; }
						if (i < FIELD_MAX_HEIGHT - 1 && save_dead_ends[i + 1][j] == 1) { save_steps[i + 1][j] += counter; save_dead_ends[i + 1][j] = -2; flag = 1; }
						if (j > 0 && save_dead_ends[i][j - 1] == 1) { save_steps[i][j - 1] += counter; save_dead_ends[i][j - 1] = -2; flag = 1; }
						if (j < FIELD_MAX_HEIGHT - 1 && save_dead_ends[i][j + 1] == 1) { save_steps[i][j + 1] += counter; save_dead_ends[i][j + 1] = -2; flag = 1; }
						save_dead_ends[i][j] = 0;
					}
				}
			}
			for (int i = 0; i < tmp_I; i++)
				for (int j = 0; j < tmp_J; j++)
					if (save_dead_ends[i][j] == -2)save_dead_ends[i][j]++;
			counter++;
		}//第二次，为胡同标记步数，记录在save_steps上；
		for (int i = 0; i < tmp_I; i++)
		{
			for (int j = tmp_J; j < Width; j++)
			{
				save_steps[i][j] = save_steps[i][Width - j - 1];
			}
		}
		for (int i = tmp_I; i < Height; i++)
		{
			for (int j = 0; j < Width; j++)
			{
				save_steps[i][j] = save_steps[Height - i - 1][j];
			}
		}//做镜面复制，从四分之一扩展成全部地图

		 /*save_steps中数据(char型)：
		 CHAR_START ：非胡同
		 CHART_START + n ：胡同里n步深度（0 < n < 40)*/
	}//——————————————————————————————————————————————————————————————

	 //侦察胡同里的豆子和敌人
	 //返回的int数值表示进胡同可以获得的力量增长收益
	int DeadEnd_Value(GameField &gameField ,int y, int x, int myID, int original_strength)//y表示第一个下标，x表示第二个下标，表示自己将要走到的那个胡同格子
	{
		int depth;//表示估测是从胡同里第几步开始的
		int Value = 0;
		int Height = gameField.height, Width = gameField.width;
		int original_y = y, original_x = x;//保存原始数据
		int enemy = -1;//记录胡同里的敌人是第几号玩家

		depth = (int)save_steps[y][x];
		if ((depth - CHAR_START))
		{
			int Flag = 1, counter = 0;
			while (Flag)
			{
				if (gameField.fieldContent[y][x] & smallFruit) Value += 1;
				else if (gameField.fieldContent[y][x] & largeFruit) Value += 10;//因为吃了大豆子可以回头吃掉来堵我的强大吃豆人，所以大豆子在此处是有用的；
				else if (gameField.fieldContent[y][x] & playerMask)
				{//看到敌人，在后面执行搜索，counter用于记录敌人数量
					counter++;
					if (gameField.fieldContent[y][x] & player1) enemy = 0;
					else if (gameField.fieldContent[y][x] & player2) enemy = 1;
					else if (gameField.fieldContent[y][x] & player3) enemy = 2;
					else if (gameField.fieldContent[y][x] & player4) enemy = 3;
					if (enemy == myID) return -100;//应该不会出现这种情况，万一出现了这种情况，为防止程序出错，就别走胡同了
				}

				if (x > 0 && (save_steps[y][x - 1] - save_steps[y][x]) == 1) x--;
				else if (y > 0 && (save_steps[y - 1][x] - save_steps[y][x]) == 1) y--;
				else if (x < (Width - 1) && (save_steps[y][x + 1] - save_steps[y][x]) == 1) x++;
				else if (y < (Height - 1) && (save_steps[y + 1][x] - save_steps[y][x]) == 1) y++;
				else Flag = 0;

			}
			if (!counter) return Value;
			else if (counter > 1) return -100;//返回-100表示进入此胡同绝对会吃亏，除非万不得已否则不走
			else if (counter == 1)
			{//开始搜索
				if (gameField.players[enemy].strength >= gameField.players[myID].strength) return -100;
				y = original_y; x = original_x;
				Value = 0;
				Pacman::Direction myAct = Pacman::up;
				Pacman::Direction rivalAct = Pacman::stay;
				int dx = 0, dy = 0, rivalcount = 0, smallest_value = 100;

				dx = 0; dy = 0;
				dx = x - gameField.players[myID].col;
				dy = y - gameField.players[myID].row;
				if (dx == 1) myAct = Pacman::right;
				else if (dx == -1) myAct = Pacman::left;
				else if (dy == 1) myAct = Pacman::down;
				else if (dy == -1) myAct = Pacman::up;//确定自己向前的一部；

				int flag = 0;
				for (rivalAct = stay; rivalAct < 4; ++rivalAct)
				{
					if (gameField.ActionValid(enemy, rivalAct))
					{
						flag = 1;
						gameField.actions[enemy] = rivalAct;
						if (gameField.ActionValid(myID, myAct)) gameField.actions[myID] = myAct;//别忘了最后回溯

						if (gameField.players[myID].dead)
						{
							gameField.PopState(); return -100;
						}
						else if (gameField.players[enemy].dead) Value = (gameField.players[enemy].strength) / 2;
						else  Value = gameField.players[myID].strength - original_strength;

						if (x > 0 && (save_steps[y][x - 1] - save_steps[y][x]) == 1) x--;
						else if (y > 0 && (save_steps[y - 1][x] - save_steps[y][x]) == 1) y--;
						else if (x < (Width - 1) && (save_steps[y][x + 1] - save_steps[y][x]) == 1) x++;
						else if (y < (Height - 1) && (save_steps[y + 1][x] - save_steps[y][x]) == 1) y++;
						else
						{
							gameField.PopState();
							return smallest_value;
						}
						Value += DeadEnd_Value(gameField,y, x, myID, gameField.players[myID].strength);	//递归

						if (Value < smallest_value) smallest_value = Value;

						gameField.PopState();
					}
				}
				return smallest_value;
			}

		}
		else return -1;//如果(depth- CHART_START)值为0（char型矩阵 save_steps中CHAR_START表示非胡同格子），表示计算的这个格子并不是胡同中的某一个格子，返回-1表示调用错误；
					   /*总结返回值：
					   n（n>=0）可以获得收益为n；
					   -1 调用错误，此处不应调用此函数
					   -2到-100 别进这条胡同！
					   */
	}
}

//Data处理
namespace Data
{
	using Pacman::GameField;
	void resetData(GameField & gameField,string & data, char *p)
	{
		int size = 1 + FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH + FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH*FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH;

		memset(p, CHAR_START, size);
		if (gameField.turnID)
		{
			strcpy(p, data.c_str());
		}
	}

	// 用于从data中获取disBetween信息
	void getRoute(char *p)
	{
		p += FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH;
		memcpy(disBetween, p, FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH*FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH);
		p -= FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH ;
	}

	// 将disBetween信息写入data中以保存
	void setRoute(char * p)
	{
		p += FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH;
		memcpy(p, disBetween, FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH*FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH);
		p -= FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH;
	}

	/* 用于存储DeadEnd信息
	请将DeadEnd信息存储在Height*Width的二位数组中
	*/
	void getDeadEnd(char * p)
	{
		memcpy(save_steps,p, FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH);
	}

	/* 用于读取DeadEnd信息
	请将DeadEnd信息一次性读取到Height*Width的二位数组中
	*/
	void setDeadEnd(char * p)
	{
		memcpy(p, save_steps, FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH);
	}
}


namespace PsychoMelon {

	// 记录搜索前原力量
	int myOriginStrength;
	int SearchCount = 0;// 记录已搜索深度

	// 记录自己行动
	// 记录估值最大的若干种行动
	// RandomAct从中随机返回一个
	struct MyBestAct {
		int score;
		int actCount;
		Pacman::Direction act[5];
		Pacman::Direction RandomAct() {// 从估值相同的行动中随机选择一个执行
			return act[Helpers::RandBetween(0, actCount)];
		}
		MyBestAct() :actCount(0) {}
	};

	// 记录对手行动
	// 调用构造函数时，直接记录在结构体中
	struct RivalAct {
		int rivalCount;
		int rivalID[3];
		int rivalActCount[3];
		int totalActCount;
		Pacman::Direction rivalAct[3][5];
		Pacman::Direction GetAction(int _, int i) {// 0<=_<rivalCount ; 0<=i<totalActCount
			switch (rivalCount) {
			case 1:return rivalAct[_][i];
			case 2:
				switch (_) {
				case 0:return rivalAct[_][i / rivalActCount[1]];
				case 1:return rivalAct[_][i % rivalActCount[1]];
				}
			case 3:
				switch (_) {
				case 0:return rivalAct[_][i / rivalActCount[1] / rivalActCount[2]];
				case 1:return rivalAct[_][i / rivalActCount[2] % rivalActCount[1]];
				case 2:return rivalAct[_][i % rivalActCount[2]];
				}
			}
		}
		RivalAct(const Pacman::GameField &gameField, int myID) {// 构造函数
																// 记录存活对手 rivalCount,rivalID
			rivalCount = 0;
			for (int _ = 0; _ < MAX_PLAYER_COUNT; ++_) {
				if (_ == myID || gameField.players[_].dead)
					continue;
				rivalID[rivalCount++] = _;
			}
			// 记录所有存活对手可能行动rivalAct
			// 所有可能情况数totalCount，最大为125(=5*5*5)
			memset(rivalActCount, 0, sizeof(rivalActCount));
			totalActCount = 1;
			Pacman::Direction d;
			for (int _ = 0; _ < rivalCount; ++_) {
				for (d = Pacman::stay; d < 4; ++d) {
					if (gameField.ActionValid(rivalID[_], d)) {
						rivalAct[_][rivalActCount[_]++] = d;
					}
				}
				totalActCount *= rivalActCount[_];
			}
		}
	};

	// 声明
	MyBestAct MyPlay(Pacman::GameField &gameField, int myID, bool ScoreOnly = true);	

						// 估值函数
	inline int CalcValue(Pacman::GameField &gameField, int myID) {
		bool hasNextTurn = gameField.NextTurn();

		if (gameField.players[myID].dead)// 死亡则立即返回
			return -1000;

		if (SearchCount == MAX_SEARCH_DEPTH || !hasNextTurn) {
			return Value::GetValue(gameField, myID) + (gameField.players[myID].strength - myOriginStrength)*Value::valueOfDistance[0];
		}
		else
			return MyPlay(gameField, myID).score;
	}


	// 自己决策
	// 返回值为MyAct结构体
	// ScoreOnly为true时只记录score，不记录act
	MyBestAct MyPlay(Pacman::GameField &gameField, int myID, bool ScoreOnly) {
		MyBestAct returnAct;// 用于返回的结构体
		if (!ScoreOnly)
			myOriginStrength = gameField.players[myID].strength;
		int bestScore = 0;
		int tmpScore = 0;

		// 模拟对手决策
		RivalAct rivalAct(gameField, myID);

		Pacman::Direction myAct = Pacman::stay;
		for (; myAct < 4; ++myAct) {
			if (gameField.ActionValid(myID, myAct)) {
				int worstScore = 10000000;
				for (int i = 0; i < rivalAct.totalActCount; ++i) {
					gameField.actions[myID] = myAct;
					for (int _ = 0; _ < rivalAct.rivalCount; ++_) {
						gameField.actions[rivalAct.rivalID[_]] = rivalAct.GetAction(_, i);
					}
					SearchCount++;
					tmpScore = CalcValue(gameField, myID);

					SearchCount--;
					if (tmpScore < worstScore) {// MIN节点
						worstScore = tmpScore;
					}
					gameField.PopState();
					if (worstScore < bestScore)// alpha剪枝
						break;
				}
				if (ScoreOnly) {
					if (worstScore > bestScore)
						bestScore = worstScore;
				}
				else {
					if (worstScore > bestScore) {// MAX节点
						bestScore = worstScore;
						returnAct.actCount = 0;
						returnAct.act[returnAct.actCount++] = myAct;
					}
					else if (worstScore == bestScore) {
						returnAct.act[returnAct.actCount++] = myAct;
					}
				}
			}
		}
		if (returnAct.actCount == 0) { // 局面惨到一步能走的都没有_(:зゝ∠)_
			returnAct.actCount = 1;
			returnAct.act[0] = Pacman::stay;
		}
		returnAct.score = bestScore;
		return returnAct;
	}
}

/*namespace Taunt {
	int DH_count=14;
	string DH[14] = {
		"Easily.",
		"Is that all?",
		"Hardly a challenge.",
		"The evil draws close.",
		"Other demons nearby?",
		"I grow differently.",
		"You dare speak to me?",
		"I'm blind, not deaf.",
		"I've been caged in darkness.",
		"My soul locks the vengeance.",
		"My brother will pay dearly for his betrayel.",
		"I've been alone for 10,000 years.",
		"You'll regret approaching me!",
		"Vengeance for my own sake!"
	};
}*/

int main()
{
	Pacman::GameField gameField;
	string data, globalData; // 这是回合之间可以传递的信息
							 // 如果在本地调试，有input.txt则会读取文件内容作为输入
							 // 如果在平台上，则不会去检查有无input.txt

	int myID = gameField.ReadInput("input.txt", data, globalData); // 输入，并获得自己ID
	int n = clock();
	Value::Initialate(gameField);
	srand(Pacman::seed + myID);
	char *p = NULL;
	int size = 1 + FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH+ FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH*FIELD_MAX_HEIGHT*FIELD_MAX_WIDTH;
	p = new char[size];

	Data::resetData(gameField,data, p);
	if (gameField.turnID)
	{
		Data::getRoute(p);
	}

	if (gameField.turnID == 0)
	{
		Value::find_dead_end(gameField);
		Data::setDeadEnd(p);
	}

	Data::getDeadEnd(p);

	Pacman::Direction myAct = PsychoMelon::MyPlay(gameField, myID, false).RandomAct();

	Data::setRoute(p);
	p[size - 1] = 0;
	data = p;
	delete[] p;

	char a[10];
	sprintf(a, "%d", (clock() - n));
	test += " ";
	test += a;

	gameField.WriteOutput(myAct, test, data, globalData);
	return 0;
}