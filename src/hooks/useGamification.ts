import { useState, useEffect, useCallback } from 'react';
import { Achievement } from '../components/Gamification/AchievementSystem';
import { LeaderboardEntry } from '../components/Gamification/Leaderboard';

interface GamificationState {
  streak: number;
  bestStreak: number;
  todayPracticed: boolean;
  achievements: Achievement[];
  totalPoints: number;
  level: number;
  leaderboard: LeaderboardEntry[];
}

const defaultAchievements: Achievement[] = [
  {
    id: 'first_session',
    title: 'Primeiros Acordes',
    description: 'Complete sua primeira sessão de prática',
    icon: '🎹',
    progress: 0,
    maxProgress: 1,
    unlocked: false,
    category: 'practice',
    points: 50,
  },
  {
    id: 'weekly_streak',
    title: 'Disciplina de Aço',
    description: 'Pratique por 7 dias seguidos',
    icon: '💪',
    progress: 0,
    maxProgress: 7,
    unlocked: false,
    category: 'consistency',
    points: 100,
  },
  {
    id: 'accuracy_master',
    title: 'Precisão Absoluta',
    description: 'Alcance 95% de precisão em uma sessão',
    icon: '🎯',
    progress: 0,
    maxProgress: 95,
    unlocked: false,
    category: 'accuracy',
    points: 75,
  },
  {
    id: 'marathon',
    title: 'Maratona Musical',
    description: 'Pratique por 30 minutos sem parar',
    icon: '🏃‍♂️',
    progress: 0,
    maxProgress: 30,
    unlocked: false,
    category: 'practice',
    points: 80,
  },
  {
    id: 'perfect_session',
    title: 'Sessão Perfeita',
    description: 'Complete uma sessão sem erros',
    icon: '⭐',
    progress: 0,
    maxProgress: 1,
    unlocked: false,
    category: 'accuracy',
    points: 150,
  },
];

export const useGamification = () => {
  const [state, setState] = useState<GamificationState>(() => {
    const saved = localStorage.getItem('piano-tutor-gamification');
    return saved
      ? JSON.parse(saved)
      : {
          streak: 0,
          bestStreak: 0,
          todayPracticed: false,
          achievements: defaultAchievements,
          totalPoints: 0,
          level: 1,
          leaderboard: [],
        };
  });

  // Salvar estado no localStorage
  useEffect(() => {
    localStorage.setItem('piano-tutor-gamification', JSON.stringify(state));
  }, [state]);

  const updateStreak = useCallback(() => {
    const today = new Date().toDateString();
    const lastPractice = localStorage.getItem('last-practice-date');

    setState(prev => {
      let newStreak = prev.streak;
      let todayPracticed = prev.todayPracticed;

      if (lastPractice !== today) {
        const yesterday = new Date();
        yesterday.setDate(yesterday.getDate() - 1);

        if (lastPractice === yesterday.toDateString()) {
          // Prática consecutiva
          newStreak += 1;
        } else if (!lastPractice || lastPractice !== today) {
          // Quebra da sequência ou primeira prática
          newStreak = 1;
        }

        localStorage.setItem('last-practice-date', today);
        todayPracticed = true;
      }

      return {
        ...prev,
        streak: newStreak,
        bestStreak: Math.max(prev.bestStreak, newStreak),
        todayPracticed,
      };
    });
  }, []);

  const unlockAchievement = useCallback((achievementId: string) => {
    setState(prev => {
      const updatedAchievements = prev.achievements.map(achievement => {
        if (achievement.id === achievementId && !achievement.unlocked) {
          return {
            ...achievement,
            unlocked: true,
            unlockedAt: new Date(),
            progress: achievement.maxProgress,
          };
        }
        return achievement;
      });

      const unlockedAchievement = updatedAchievements.find(a => a.id === achievementId);
      const pointsEarned = unlockedAchievement?.points || 0;
      const newTotalPoints = prev.totalPoints + pointsEarned;
      const newLevel = Math.floor(newTotalPoints / 100) + 1;

      // Mostrar notificação (simulada)
      if (unlockedAchievement) {
        console.log(`🎉 Conquista desbloqueada: ${unlockedAchievement.title}`);
      }

      return {
        ...prev,
        achievements: updatedAchievements,
        totalPoints: newTotalPoints,
        level: newLevel,
      };
    });
  }, []);

  const updateAchievementProgress = useCallback((achievementId: string, progress: number) => {
    setState(prev => {
      const updatedAchievements = prev.achievements.map(achievement => {
        if (achievement.id === achievementId && !achievement.unlocked) {
          const newProgress = Math.min(progress, achievement.maxProgress);
          const shouldUnlock = newProgress >= achievement.maxProgress;

          return {
            ...achievement,
            progress: newProgress,
            unlocked: shouldUnlock,
            ...(shouldUnlock && { unlockedAt: new Date() }),
          };
        }
        return achievement;
      });

      // Verificar se alguma conquista foi desbloqueada
      const unlockedAchievement = updatedAchievements.find(
        a =>
          a.id === achievementId &&
          a.unlocked &&
          !prev.achievements.find(pa => pa.id === achievementId && pa.unlocked)
      );

      if (unlockedAchievement) {
        const pointsEarned = unlockedAchievement.points;
        const newTotalPoints = prev.totalPoints + pointsEarned;
        const newLevel = Math.floor(newTotalPoints / 100) + 1;

        console.log(`🎉 Conquista desbloqueada: ${unlockedAchievement.title}`);

        return {
          ...prev,
          achievements: updatedAchievements,
          totalPoints: newTotalPoints,
          level: newLevel,
        };
      }

      return {
        ...prev,
        achievements: updatedAchievements,
      };
    });
  }, []);

  const recordSession = useCallback(
    (sessionData: { duration: number; accuracy: number; hasErrors: boolean }) => {
      updateStreak();

      // Atualizar progresso das conquistas
      updateAchievementProgress('first_session', 1);

      if (sessionData.duration >= 30) {
        updateAchievementProgress('marathon', sessionData.duration);
      }

      if (sessionData.accuracy >= 95) {
        updateAchievementProgress('accuracy_master', sessionData.accuracy);
      }

      if (!sessionData.hasErrors) {
        updateAchievementProgress('perfect_session', 1);
      }

      // Atualizar sequência semanal
      updateAchievementProgress('weekly_streak', state.streak);
    },
    [updateStreak, updateAchievementProgress, state.streak]
  );

  const loadLeaderboard = useCallback(
    async (_timeFrame: 'daily' | 'weekly' | 'monthly' | 'allTime') => {
      // Simular carregamento do leaderboard
      const mockLeaderboard: LeaderboardEntry[] = [
        {
          userId: '1',
          username: 'PianoMaster',
          score: 12500,
          level: 13,
          streak: 45,
          accuracy: 0.92,
          rank: 1,
        },
        {
          userId: '2',
          username: 'MusicLover',
          score: 9800,
          level: 10,
          streak: 23,
          accuracy: 0.87,
          rank: 2,
        },
        {
          userId: '3',
          username: 'Você',
          score: state.totalPoints,
          level: state.level,
          streak: state.streak,
          accuracy: 0.85,
          rank: 3,
          isCurrentUser: true,
        },
        {
          userId: '4',
          username: 'BeginnerPro',
          score: 4200,
          level: 5,
          streak: 7,
          accuracy: 0.78,
          rank: 4,
        },
      ];

      setState(prev => ({
        ...prev,
        leaderboard: mockLeaderboard,
      }));
    },
    [state.totalPoints, state.level, state.streak]
  );

  return {
    ...state,
    updateStreak,
    unlockAchievement,
    updateAchievementProgress,
    recordSession,
    loadLeaderboard,
  };
};
