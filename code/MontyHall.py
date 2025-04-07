# Monty Hall Simulation: Zeitlicher Verlauf der Gewinnwahrscheinlichkeit

import numpy as np
import matplotlib.pyplot as plt

def simulate_monty_hall_progress(num_trials, switch=True):
    """
    Simuliert das Monty-Hall-Problem für eine gegebene Anzahl an Durchläufen und
    verfolgt den zeitlichen Verlauf der kumulativen Gewinnwahrscheinlichkeit.
    
    Parameter:
    - num_trials: Anzahl der Simulationen
    - switch: Bool, ob der Kandidat die Tür wechselt (True) oder nicht (False)
    
    Rückgabe:
    - Eine Liste mit der kumulativen Gewinnwahrscheinlichkeit nach jedem Durchlauf.
    """
    wins = 0
    win_rates = []
    doors = np.array([0, 1, 2])
    
    for i in range(num_trials):
        # Preis zufällig hinter einer Tür platzieren
        prize = np.random.randint(0, 3)
        # Kandidat wählt zufällig eine Tür
        choice = np.random.randint(0, 3)
        
        # Moderator öffnet eine Tür, die weder gewählt noch der Preis ist
        if choice == prize:
            available = np.setdiff1d(doors, [choice])
            door_opened = np.random.choice(available)
        else:
            available = np.setdiff1d(doors, [choice, prize])
            door_opened = available[0]
        
        # Kandidat entscheidet sich: wechseln oder bleiben
        if switch:
            new_choice = np.setdiff1d(doors, [choice, door_opened])[0]
            final_choice = new_choice
        else:
            final_choice = choice
        
        # Gewinn auswerten
        if final_choice == prize:
            wins += 1
        
        # Kumulative Gewinnwahrscheinlichkeit nach i+1 Durchläufen
        win_rates.append(wins / (i + 1))
        
    return win_rates

# Anzahl der Durchläufe
num_trials = 2000

# Berechnung des zeitlichen Verlaufs für beide Strategien
win_rates_switch = simulate_monty_hall_progress(num_trials, switch=True)
win_rates_stay   = simulate_monty_hall_progress(num_trials, switch=False)

# Endergebnisse ausgeben
print("Anzahl der Durchläufe:", num_trials)
print("Endgültige Gewinnchance bei Wechsel (Bleiben): {:.2%}".format(win_rates_switch[-1]))
print("Endgültige Gewinnchance bei Beibehalten (Wechseln): {:.2%}".format(win_rates_stay[-1]))

# Visualisierung des zeitlichen Verlaufs
plt.figure(figsize=(10, 6))
plt.plot(win_rates_switch, label='Bleiben', lw=1)
plt.plot(win_rates_stay, label='Wechseln', lw=1)
plt.xlabel('Anzahl der Durchläufe')
plt.ylabel('Kumulative Gewinnwahrscheinlichkeit')
plt.title('Zeitlicher Verlauf der Gewinnwahrscheinlichkeit im Monty-Hall-Problem')
plt.legend()
plt.grid(True)
plt.show()
