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

#define FIELD_MAX_HEIGHT 20
#define FIELD_MAX_WIDTH 20
#define MAX_GENERATOR_COUNT 4 // ÿ������1
#define MAX_PLAYER_COUNT 4
#define MAX_TURN 100


// ��Ҳ����ѡ�� using namespace std; ���ǻ���Ⱦ�����ռ�
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
[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH]; // ��������Ӷ�(�����ж��Ƿ�����)

// ƽ̨�ṩ�ĳԶ�������߼��������
namespace Pacman
{
	const time_t seed = time(0);
	const int dx[] = { 0, 1, 0, -1, 1, 1, -1, -1 }, dy[] = { -1, 0, 1, 0, -1, 1, 1, -1 };

	// ö�ٶ��壻ʹ��ö����Ȼ���˷ѿռ䣨sizeof(GridContentType) == 4�������Ǽ��������32λ������Ч�ʸ���

	// ÿ�����ӿ��ܱ仯�����ݣ�����á����߼��������
	enum GridContentType
	{
		empty = 0, // ��ʵ�����õ�
		player1 = 1, // 1�����
		player2 = 2, // 2�����
		player3 = 4, // 3�����
		player4 = 8, // 4�����
		playerMask = 1 | 2 | 4 | 8, // ���ڼ����û����ҵ�
		smallFruit = 16, // С����
		largeFruit = 32 // ����
	};

	// �����ID��ȡ��������ҵĶ�����λ
	GridContentType playerID2Mask[] = { player1, player2, player3, player4 };
	string playerID2str[] = { "0", "1", "2", "3" };

	// ��ö��Ҳ��������Щ�����ˣ����ӻ�������
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

	// ÿ�����ӹ̶��Ķ���������á����߼��������
	enum GridStaticType
	{
		emptyWall = 0, // ��ʵ�����õ�
		wallNorth = 1, // ��ǽ����������ٵķ���
		wallEast = 2, // ��ǽ�����������ӵķ���
		wallSouth = 4, // ��ǽ�����������ӵķ���
		wallWest = 8, // ��ǽ����������ٵķ���
		generator = 16 // ���Ӳ�����
	};

	// ���ƶ�����ȡ����������赲�ŵ�ǽ�Ķ�����λ
	GridStaticType direction2OpposingWall[] = { wallNorth, wallEast, wallSouth, wallWest };

	// ���򣬿��Դ���dx��dy���飬ͬʱҲ������Ϊ��ҵĶ���
	enum Direction
	{
		stay = -1,
		up = 0,
		right = 1,
		down = 2,
		left = 3,
		// ������⼸��ֻ��Ϊ�˲��������򷽱㣬����ʵ���õ�
		ur = 4, // ����
		dr = 5, // ����
		dl = 6, // ����
		ul = 7 // ����
	};

	// �����ϴ�����������
	struct FieldProp
	{
		int row, col;
	};

	// �����ϵ����
	struct Player : FieldProp
	{
		int strength;
		int powerUpLeft;
		bool dead;
	};

	// �غ��²����Ķ��ӵ�����
	struct NewFruits
	{
		FieldProp newFruits[MAX_GENERATOR_COUNT * 8];
		int newFruitCount;
	} newFruits[MAX_TURN];
	int newFruitsCount = 0;

	// ״̬ת�Ƽ�¼�ṹ
	struct TurnStateTransfer
	{
		enum StatusChange // �����
		{
			none = 0,
			ateSmall = 1,
			ateLarge = 2,
			powerUpCancel = 4,
			die = 8,
			error = 16
		};

		// ���ѡ���Ķ���
		Direction actions[MAX_PLAYER_COUNT];

		// �˻غϸ���ҵ�״̬�仯
		StatusChange change[MAX_PLAYER_COUNT];

		// �˻غϸ���ҵ������仯
		int strengthDelta[MAX_PLAYER_COUNT];
	};

	// ��Ϸ��Ҫ�߼������࣬��������������غ����㡢״̬ת�ƣ�ȫ��Ψһ
	class GameField
	{
	private:
		// Ϊ�˷��㣬��������Զ�����private��

		// ��¼ÿ�غϵı仯��ջ��
		TurnStateTransfer backtrack[MAX_TURN];

		// ��������Ƿ��Ѿ�����
		static bool constructed;

	public:
		// ���صĳ��Ϳ�
		int height, width;
		int generatorCount;
		int GENERATOR_INTERVAL, LARGE_FRUIT_DURATION, LARGE_FRUIT_ENHANCEMENT;

		// ���ظ��ӹ̶�������
		GridStaticType fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];

		// ���ظ��ӻ�仯������
		GridContentType fieldContent[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];
		int generatorTurnLeft; // ���ٻغϺ��������
		int aliveCount; // �ж�����Ҵ��
		int smallFruitCount;
		int turnID;
		FieldProp generators[MAX_GENERATOR_COUNT]; // ����Щ���Ӳ�����
		Player players[MAX_PLAYER_COUNT]; // ����Щ���

										  // ���ѡ���Ķ���
		Direction actions[MAX_PLAYER_COUNT];

		// �ָ����ϴγ���״̬������һ·�ָ����ʼ��
		// �ָ�ʧ�ܣ�û��״̬�ɻָ�������false
		bool PopState()
		{
			if (turnID <= 0)
				return false;

			const TurnStateTransfer &bt = backtrack[--turnID];
			int i, _;

			// �������ָ�״̬

			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				GridContentType &content = fieldContent[_p.row][_p.col];
				TurnStateTransfer::StatusChange change = bt.change[_];

				if (!_p.dead)
				{
					// 5. �󶹻غϻָ�
					if (_p.powerUpLeft || change & TurnStateTransfer::powerUpCancel)
						_p.powerUpLeft++;

					// 4. �³�����
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

				// 2. �������
				if (change & TurnStateTransfer::die)
				{
					_p.dead = false;
					aliveCount++;
					content |= playerID2Mask[_];
				}

				// 1. ���λ�Ӱ
				if (!_p.dead && bt.actions[_] != stay)
				{
					fieldContent[_p.row][_p.col] &= ~playerID2Mask[_];
					_p.row = (_p.row - dy[bt.actions[_]] + height) % height;
					_p.col = (_p.col - dx[bt.actions[_]] + width) % width;
					fieldContent[_p.row][_p.col] |= playerID2Mask[_];
				}

				// 0. ���겻�Ϸ������
				if (change & TurnStateTransfer::error)
				{
					_p.dead = false;
					aliveCount++;
					content |= playerID2Mask[_];
				}

				// *. �ָ�����
				if (!_p.dead)
					_p.strength -= bt.strengthDelta[_];
			}

			// 3. �ջض���
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

		// �ж�ָ�������ָ�������ƶ��ǲ��ǺϷ��ģ�û��ײǽ��
		inline bool ActionValid(int playerID, Direction &dir) const
		{
			if (dir == stay)
				return true;
			const Player &p = players[playerID];
			const GridStaticType &s = fieldStatic[p.row][p.col];
			return dir >= -1 && dir < 4 && !(s & direction2OpposingWall[dir]);
		}

		// ����actionsд����Ҷ�����������һ�غϾ��棬����¼֮ǰ���еĳ���״̬���ɹ��պ�ָ���
		// ���վֵĻ��ͷ���false
		bool NextTurn()
		{
			int _, i, j;

			TurnStateTransfer &bt = backtrack[turnID];
			memset(&bt, 0, sizeof(bt));

			// 0. ɱ�����Ϸ�����
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
						// �������Լ�ǿ��׳������ǲ���ǰ����
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

			// 1. λ�ñ仯
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				bt.actions[_] = actions[_];

				if (actions[_] == stay)
					continue;

				// �ƶ�
				fieldContent[_p.row][_p.col] &= ~playerID2Mask[_];
				_p.row = (_p.row + dy[actions[_]] + height) % height;
				_p.col = (_p.col + dx[actions[_]] + width) % width;
				fieldContent[_p.row][_p.col] |= playerID2Mask[_];
			}

			// 2. ��һ�Ź
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				// �ж��Ƿ��������һ��
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

					// ��Щ��ҽ��ᱻɱ��
					int lootedStrength = 0;
					for (i = begin; i < containedCount; i++)
					{
						int id = containedPlayers[i];
						Player &p = players[id];

						// �Ӹ���������
						fieldContent[p.row][p.col] &= ~playerID2Mask[id];
						p.dead = true;
						int drop = p.strength / 2;
						bt.strengthDelta[id] += -drop;
						bt.change[id] |= TurnStateTransfer::die;
						lootedStrength += drop;
						p.strength -= drop;
						aliveCount--;
					}

					// ������������
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

			// 3. ��������
			if (--generatorTurnLeft == 0)
			{
				generatorTurnLeft = GENERATOR_INTERVAL;
				NewFruits &fruits = newFruits[newFruitsCount++];
				fruits.newFruitCount = 0;
				for (i = 0; i < generatorCount; i++)
					for (Direction d = up; d < 8; ++d)
					{
						// ȡ�࣬�������ر߽�
						int r = (generators[i].row + dy[d] + height) % height, c = (generators[i].col + dx[d] + width) % width;
						if (fieldStatic[r][c] & generator || fieldContent[r][c] & (smallFruit | largeFruit))
							continue;
						fieldContent[r][c] |= smallFruit;
						fruits.newFruits[fruits.newFruitCount].row = r;
						fruits.newFruits[fruits.newFruitCount++].col = c;
						smallFruitCount++;
					}
			}

			// 4. �Ե�����
			for (_ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				Player &_p = players[_];
				if (_p.dead)
					continue;

				GridContentType &content = fieldContent[_p.row][_p.col];

				// ֻ���ڸ�����ֻ���Լ���ʱ����ܳԵ�����
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

			// 5. �󶹻غϼ���
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

			// �Ƿ�ֻʣһ�ˣ�
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

			// �Ƿ�غϳ��ޣ�
			if (turnID >= 100)
				return false;

			return true;
		}

		// ��ȡ�������������룬���ص��Ի��ύƽ̨ʹ�ö����ԡ�
		// ����ڱ��ص��ԣ�����������Ŷ�ȡ������ָ�����ļ���Ϊ�����ļ���ʧ�ܺ���ѡ��ȴ��û�ֱ�����롣
		// ���ص���ʱ���Խ��ܶ����Ա������Windows�¿����� Ctrl-Z ��һ��������+�س�����ʾ���������������������ֻ����ܵ��м��ɡ�
		// localFileName ����ΪNULL
		// obtainedData ������Լ��ϻغϴ洢�����غ�ʹ�õ�����
		// obtainedGlobalData ������Լ��� Bot ����ǰ�洢������
		// ����ֵ���Լ��� playerID
		int ReadInput(const char *localFileName, string &obtainedData, string &obtainedGlobalData)
		{
			string str, chunk;
#ifdef _BOTZONE_ONLINE
			std::ios::sync_with_stdio(false); //��\\)
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

			// ��ȡ���ؾ�̬״��
			Json::Value field = input["requests"][(Json::Value::UInt) 0],
				staticField = field["static"], // ǽ��Ͳ�����
				contentField = field["content"]; // ���Ӻ����
			height = field["height"].asInt();
			width = field["width"].asInt();
			LARGE_FRUIT_DURATION = field["LARGE_FRUIT_DURATION"].asInt();
			LARGE_FRUIT_ENHANCEMENT = field["LARGE_FRUIT_ENHANCEMENT"].asInt();
			generatorTurnLeft = GENERATOR_INTERVAL = field["GENERATOR_INTERVAL"].asInt();

			PrepareInitialField(staticField, contentField);

			// ������ʷ�ָ�����
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

		// ���� static �� content ����׼�����صĳ�ʼ״��
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

		// ��ɾ��ߣ���������
		// action ��ʾ���غϵ��ƶ�����stay Ϊ���ƶ�
		// tauntText ��ʾ��Ҫ��������������������ַ�����������ʾ����Ļ�ϲ������κ����ã����ձ�ʾ������
		// data ��ʾ�Լ���洢����һ�غ�ʹ�õ����ݣ����ձ�ʾɾ��
		// globalData ��ʾ�Լ���洢���Ժ�ʹ�õ����ݣ��滻����������ݿ��Կ�Ծ�ʹ�ã���һֱ������� Bot �ϣ����ձ�ʾɾ��
		void WriteOutput(Direction action, string tauntText = "", string data = "", string globalData = "") const
		{
			Json::Value ret;
			ret["response"]["action"] = action;
			ret["response"]["tauntText"] = tauntText;
			ret["data"] = data;
			ret["globaldata"] = globalData;
			ret["debug"] = (Json::Int)seed;

#ifdef _BOTZONE_ONLINE
			Json::FastWriter writer; // ��������Ļ����þ��С���
#else
			Json::StyledWriter writer; // ���ص��������ÿ� > <
#endif
			cout << writer.write(ret) << endl;
		}

		// ������ʾ��ǰ��Ϸ״̬�������á�
		// �ύ��ƽ̨��ᱻ�Ż�����
		inline void DebugPrint() const
		{
#ifndef _BOTZONE_ONLINE
			printf("�غϺš�%d�����������%d��| ͼ�� ������[G] �����[0/1/2/3] ������[*] ��[o] С��[.]\n", turnID, aliveCount);
			for (int _ = 0; _ < MAX_PLAYER_COUNT; _++)
			{
				const Player &p = players[_];
				printf("[���%d(%d, %d)|����%d|�ӳ�ʣ��غ�%d|%s]\n",
					_, p.row, p.col, p.strength, p.powerUpLeft, p.dead ? "����" : "���");
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

		// ��ʼ����Ϸ������
		GameField()
		{
			if (constructed)
				throw runtime_error("�벻Ҫ�ٴ��� GameField �����ˣ�����������ֻӦ����һ������");
			constructed = true;

			turnID = 0;
		}

		GameField(const GameField &b) : GameField() { }
	};

	bool GameField::constructed = false;
}

// һЩ��������
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
			// ��ÿ�������������ĺϷ�����
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

			// ����һ������仯
			// NextTurn����true��ʾ��Ϸû�н���
			bool hasNext = gameField.NextTurn();
			count++;

			if (!hasNext)
				break;
		}

		// �������
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

		// �ָ���Ϸ״̬����������Ǳ��غϣ�
		while (count-- > 0)
			gameField.PopState();
	}
}

// Phycho-Melon AI
// started at 2016-5-1

#define MAX_SEARCH_DEPTH 2 // ���������������
#define MAX_DISTANCE 20 // ��¼��������

namespace Value {
	using namespace Pacman;
	// Distance

	int height, width;
	GridContentType fieldContent[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];
	GridStaticType fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];

											 // ÿ�غϿ�ʼ��Ҫ����һ��
	void Initialate(GameField &gameField) {
		height = gameField.height;
		width = gameField.width;
		memcpy(fieldContent, gameField.fieldContent, sizeof(gameField.fieldContent));
		memcpy(fieldStatic, gameField.fieldStatic, sizeof(gameField.fieldStatic));
		memset(disBetween, 1, sizeof(disBetween));
	}
	// ����ĳ����Χ�������
	void SetDis(char(*p)[FIELD_MAX_WIDTH], char dis) {
		for (int i = 0; i < height; i++)
			for (int j = 0; j < width; j++) {
				if (p[i][j] == dis) {
					GridStaticType &s = fieldStatic[i][j];
					for (Direction dir = up; dir < 4; ++dir) {
						if (!(s&direction2OpposingWall[dir])) {
							char &_p = p[(i + dy[dir] + height) % height][(j + dx[dir] + width) % width];
							if (_p == 1 || _p > dis + 1)
								_p = dis + 1;
						}
					}
				}
			}
		if (dis + 1 >= MAX_DISTANCE)return;
		SetDis(p, dis + 1);
	}

	// ��¼����
	void RecordDisBetween(int row1, int col1, int row2, int col2, int dis) {
		disBetween[row1][col1][row2][col2] = dis;
		disBetween[row2][col2][row1][col1] = dis;
		disBetween[height - row1][col1][height - row2][col2] = dis;
		disBetween[height - row2][col2][height - row1][col1] = dis;
		disBetween[row1][width - col1][row2][width - col2] = dis;
		disBetween[row2][width - col2][row1][width - col1] = dis;
		disBetween[height - row1][width - col1][height - row2][width - col2] = dis;
		disBetween[height - row2][width - col2][height - row1][width - col1] = dis;
	}

	// �����������룬-1��ʾ�������㷶Χ
	int GetDisBetween(int row1, int col1, int row2, int col2) {
		char(*p1)[FIELD_MAX_WIDTH] = disBetween[row1][col1];
		char(*p2)[FIELD_MAX_WIDTH] = disBetween[row2][col2];
		if (p1[row1][col1] == 1) { // �õ㻹δ�����
			p1[row1][col1] = 2;
			SetDis(p1, 2);
		}

		if (p2[row2][col2] == 1) {
			p2[row2][col2] = 2;
			SetDis(p2, 2);
		}

		// ���������Ѽ�¼��
		if (p1[row2][col2] > 1)
			return p1[row2][col2] - 2;
		// ��������δ��¼��
		int minDis = 201;
		for (int i = 0; i < height; i++)
			for (int j = 0; j < width; j++) {
				if (p1[i][j] && p2[i][j]) {
					int tmp = p1[i][j] + p2[i][j];
					if (tmp < minDis)
						minDis = tmp;
				}
			}
		if (minDis < 201) {
			int tmp = minDis - 2;
			RecordDisBetween(row1, col1, row2, col2, tmp);
			return tmp - 2;
		}
		else
			return -1; // �������㷶Χ
	}

	const int valueOfDistance[40] = { 89,55,34,21,13,8,5,3,2,1,0 };

	int GetValue(GameField &gameField, int myID) {
		int value = 0;
		Player &p = gameField.players[myID];
		/*
		// ��¼������
		Player rival_p[3];
		int rivalCount = 0;
		for (int i = 0; i < 4; ++i) {
			if (i != myID&&gameField.players[i].dead == false)
				rival_p[rivalCount++] = gameField.players[i];
		}
		// ��ͬ�ж�
		if (save_steps[p.row][p.col] < 100) {

		}
		*/


		// �Զ���ֵ
		for (int i = 0; i < height; ++i) {
			for (int j = 0; j < width; ++j) {
				if (gameField.fieldContent[i][j] & smallFruit) {
					int dis = GetDisBetween(p.row, p.col, i, j);
					if (dis >= 0)
						value += valueOfDistance[dis];
				}
			}
		}
		return value;
	}
	
	//��¼����ͬ��������������������������������������������������������������������������������������������

	char save_steps[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//���յõ��ļ�¼

	void find_dead_end(Pacman::GameField gameField)
	{
		int Height = gameField.height, Width = gameField.width;
		int tmp_I = Height / 2 + Height % 2, tmp_J = Width / 2 + Width % 2;

		int save_dead_ends[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//��Ǻ�ͬ�����
		int tmp_fieldStatic[FIELD_MAX_HEIGHT][FIELD_MAX_WIDTH];//��¼��ͼ��Ϣ�������

		for (int i = 0; i < FIELD_MAX_HEIGHT; i++)
		{
			for (int j = 0; j < FIELD_MAX_WIDTH; j++)
			{
				save_dead_ends[i][j] = 0;
				save_steps[i][j] = 100;
			}
		}//��ʼ��
		for (int i = 0; i < Height; i++)
			for (int j = 0; j < Width; j++) tmp_fieldStatic[i][j] = gameField.fieldStatic[i][j];
		//��gamefield��ȡ��ͼ��Ϣ

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
		}//��һ�Σ��ҳ���ͬ������ǣ���¼��save_dead_end��
		 /*
		 save_dead_end�������ͣ�int��
		 0�����ں�ͬ��һ���߲�����ͬ
		 -1��һ���п����ߵ���ͬ
		 1��hutong*/

		counter = 1; flag = 1;//counter��¼��ͬ���
		while (flag)
		{
			flag = 0;
			for (int i = 0; i < tmp_I; i++)
			{
				for (int j = 0; j < tmp_J; j++)
				{
					if (save_dead_ends[i][j] == -1)
					{
						if (i > 0 && save_dead_ends[i - 1][j] == 1) { save_steps[i - 1][j] = counter; save_dead_ends[i - 1][j] = -2; flag = 1; }
						if (i < FIELD_MAX_HEIGHT - 1 && save_dead_ends[i + 1][j] == 1) { save_steps[i + 1][j] = counter; save_dead_ends[i + 1][j] = -2; flag = 1; }
						if (j > 0 && save_dead_ends[i][j - 1] == 1) { save_steps[i][j - 1] = counter; save_dead_ends[i][j - 1] = -2; flag = 1; }
						if (j < FIELD_MAX_HEIGHT - 1 && save_dead_ends[i][j + 1] == 1) { save_steps[i][j + 1] = counter; save_dead_ends[i][j + 1] = -2; flag = 1; }
						save_dead_ends[i][j] = 0;
					}
				}
			}
			for (int i = 0; i < tmp_I; i++)
				for (int j = 0; j < tmp_J; j++)
					if (save_dead_ends[i][j] == -2)save_dead_ends[i][j]++;
			counter++;
		}//�ڶ��Σ�Ϊ��ͬ��ǲ�������¼��save_steps�ϣ�
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
		}//�����渴�ƣ����ķ�֮һ��չ��ȫ����ͼ

		 /*save_steps������(char��)��
		 100 ���Ǻ�ͬ
		 n ����ͬ��n����ȣ�0 < n < 40)*/
	}//����������������������������������������������������������������������������������������������������������������������������
}

//Data����
namespace Data
{
	using namespace Pacman;
	void resetData(GameField &gameField, string & data, char *p)
	{
		int height = gameField.height;
		int width = gameField.width;
		int si = sizeof(int);
		int size = (1 + 1 + height*width + height*width*height*width) * si;

		memset(p, 0, size);
		memcpy(p, &height, si);
		p += si;
		memcpy(p, &width, si);
		p -= si;
		if (gameField.turnID)
		{
			memcpy(p, data.c_str(), size);
		}
	}

	// ���ڴ�data�л�ȡdisBetween��Ϣ
	void getRoute(GameField &g, char *p)
	{
		int height = g.height;
		int width = g.width;
		int si = sizeof(int);

		int size = (1 + 1 + height*width + height*width*height*width) * si;

		memcpy(&height, p, si);
		p += si;
		memcpy(&width, p, si);
		p -= si;

		p += (1 + 1 + height*width) * si;

		for (int i = 0; i < height; i++)
		{
			for (int j = 0; j < width; j++)
			{
				for (int k = 0; k < height; k++)
				{
					memcpy(disBetween[i][j][k], p, si*width);
					p += si*width;
					for (int _k = 0; _k < width; _k++)
					{
						if (disBetween[i][j][k][_k])
						{
							test = "good";
						}
					}
				}
			}
		}
		p -= size;
	}

	// ��disBetween��Ϣд��data���Ա���
	void setRoute(GameField &g, char * p)
	{
		int height = g.height;
		int width = g.width;
		int si = sizeof(int);

		memcpy(p, &height, si);
		p += si;
		memcpy(p, &width, si);
		p -= si;
		int size = (1 + 1 + height*width + height*width*height*width) * si;

		p += (1 + 1 + height*width) * si;

		for (int i = 0; i < height; i++)
		{
			for (int j = 0; j < width; j++)
			{
				for (int k = 0; k < height; k++)
				{
					memcpy(p, disBetween[i][j][k], si*width);
					p += si*width;
					for (int _k = 0; _k < width; _k++)
					{
						if (disBetween[i][j][k][_k])
						{
							test = "bad";
						}
					}
				}
			}
		}
		p -= size;
	}

	/* ���ڴ洢DeadEnd��Ϣ
	�뽫DeadEnd��Ϣ�洢��Height*Width�Ķ�λ������
	����1 data: �洢λ��string data| ����2 deadEnd: �洢�����deadend��Ϣ��int**ָ��(����û����ĵ㣬�޺�ͬ�ĵ㣬������ѡ������������ʾ)
	*/
	void DeadEnd(string & data, const int ** deadEnd)
	{
		int height;
		int width;
		char *p;
		int si = sizeof(int);
		p = const_cast<char*>(data.c_str());

		memcpy(&height, p, si);
		p += si;
		memcpy(&width, p, si);
		p -= si;

		p += (1 + 1) * si;

		for (int i = 0; i < height; i++)
		{
			memcpy(p, deadEnd[i], si*width);
			p += si*width;
		}
	}

	/* ���ڶ�ȡDeadEnd��Ϣ
	�뽫DeadEnd��Ϣһ���Զ�ȡ��Height*Width�Ķ�λ������
	����1 data: Դλ��string data| ����2 deadEnd: ���ڴ洢deadend��Ϣ��int**ָ��
	*/
	void DeadEnd(string & data, int ** deadEnd)
	{
		int height;
		int width;
		char *p;
		int si = sizeof(int);
		p = const_cast<char*>(data.c_str());

		memcpy(&height, p, si);
		p += si;
		memcpy(&width, p, si);
		p -= si;

		p += (1 + 1) * si;

		for (int i = 0; i < height; i++)
		{
			memcpy(deadEnd[i], p, si*width);
			p += si*width;
		}
	}
}


namespace PsychoMelon {

	// ��¼����ǰԭ����
	int myOriginStrength;

	// ��¼�Լ��ж�
	// ��¼��ֵ�����������ж�
	// RandomAct�����������һ��
	struct MyBestAct {
		int score;
		int actCount;
		Pacman::Direction act[5];
		Pacman::Direction RandomAct() {// �ӹ�ֵ��ͬ���ж������ѡ��һ��ִ��
			return act[Helpers::RandBetween(0, actCount)];
		}
		MyBestAct() :actCount(0) {}
	};

	// ��¼�����ж�
	// ���ù��캯��ʱ��ֱ�Ӽ�¼�ڽṹ����
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
		RivalAct(const Pacman::GameField &gameField, int myID) {// ���캯��
																// ��¼������ rivalCount,rivalID
			rivalCount = 0;
			for (int _ = 0; _ < MAX_PLAYER_COUNT; ++_) {
				if (_ == myID || gameField.players[_].dead)
					continue;
				rivalID[rivalCount++] = _;
			}
			// ��¼���д����ֿ����ж�rivalAct
			// ���п��������totalCount�����Ϊ125(=5*5*5)
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

	// ����
	MyBestAct MyPlay(Pacman::GameField &gameField, int myID, bool ScoreOnly = true);

	int SearchCount = 0;// ��¼���������

						// ��ֵ����
	inline int CalcValue(Pacman::GameField &gameField, int myID) {
		bool hasNextTurn = gameField.NextTurn();

		if (gameField.players[myID].dead)// ��������������
			return -1000;

		if (SearchCount == MAX_SEARCH_DEPTH || !hasNextTurn) {
			return Value::GetValue(gameField, myID) + (gameField.players[myID].strength - myOriginStrength)*Value::valueOfDistance[0];
		}
		else
			return MyPlay(gameField, myID).score;
	}


	// �Լ�����
	// ����ֵΪMyAct�ṹ��
	// ScoreOnlyΪtrueʱֻ��¼score������¼act
	MyBestAct MyPlay(Pacman::GameField &gameField, int myID, bool ScoreOnly) {
		MyBestAct returnAct;// ���ڷ��صĽṹ��
		if (!ScoreOnly)
			myOriginStrength = gameField.players[myID].strength;
		int bestScore = 0;
		int tmpScore = 0;

		// ģ����־���
		RivalAct rivalAct(gameField, myID);

		Pacman::Direction myAct = Pacman::stay;
		for (; myAct < 4; ++myAct) {
			if (gameField.ActionValid(myID, myAct)) {
				int worstScore = 100000;
				for (int i = 0; i < rivalAct.totalActCount; ++i) {
					gameField.actions[myID] = myAct;
					for (int _ = 0; _ < rivalAct.rivalCount; ++_) {
						gameField.actions[rivalAct.rivalID[_]] = rivalAct.GetAction(_, i);
					}
					SearchCount++;
					tmpScore = CalcValue(gameField, myID);
					SearchCount--;
					if (tmpScore < worstScore) {// MIN�ڵ�
						worstScore = tmpScore;
					}
					gameField.PopState();
					if (worstScore < bestScore)// alpha��֦
						break;
				}
				if (ScoreOnly) {
					if (worstScore > bestScore)
						bestScore = worstScore;
				}
				else {
					if (worstScore > bestScore) {// MAX�ڵ�
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
		if (returnAct.actCount == 0) { // ����ҵ�һ�����ߵĶ�û��_(:�٩f��)_
			returnAct.actCount = 1;
			returnAct.act[0] = Pacman::stay;
		}
		returnAct.score = bestScore;
		return returnAct;
	}
}

namespace Taunt {
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
}

int main()
{
	Pacman::GameField gameField;
	string data, globalData; // ���ǻغ�֮����Դ��ݵ���Ϣ
							 // ����ڱ��ص��ԣ���input.txt����ȡ�ļ�������Ϊ����
							 // �����ƽ̨�ϣ��򲻻�ȥ�������input.txt

	int myID = gameField.ReadInput("input.txt", data, globalData); // ���룬������Լ�ID
	int n = clock();
	Value::Initialate(gameField);
	srand(Pacman::seed + myID);
	/*
	char *p = NULL;
	int size = (1 + 1 + gameField.height*gameField.width + gameField.height*gameField.width*gameField.height*gameField.width) * sizeof(int);
	p = new char[size];
	Data::resetData(gameField, globalData, p);
	if (p)
	{
		test += " get";
		Data::getRoute(gameField, p);
	}
	*/
	Pacman::Direction myAct = PsychoMelon::MyPlay(gameField, myID, false).RandomAct();
	/*
	if (p)
	{
		test += " set";
		Data::setRoute(gameField, p);
	}

	if (p)
	{
		test += " gD";
		globalData = p;
	}

	if (p)
		delete[] p;

	char a[10];

	sprintf(a, "%d", (clock() - n));
	test += " ";
	test += a;
	*/
	gameField.WriteOutput(myAct, Taunt::DH[Helpers::RandBetween(0,Taunt::DH_count)], data, globalData);
	return 0;
}