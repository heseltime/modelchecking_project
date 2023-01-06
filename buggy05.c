#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

// the data structure containing the state of the keypad
typedef struct {
    uint32_t pin;
    uint8_t state[6];
} keypad;

// new_keypad(pin) returns a keypad data structure in the Locked state with 0 attempts and stored PIN `pin`
keypad new_keypad(uint32_t pin) {
// creates a new keypad with the input PIN
    keypad kp = {pin, {0, 0, 0, 0, 0, 1}};
    return kp;
}

// digit_key(&kp, n) modifies the state of the keypad `kp` as though the digit key `n` had been pressed
void digit_key(keypad *kp, uint8_t n) {
    if (kp->state[5] <= 4) {
        kp->state[0] += 1;
        uint32_t index = kp->state[0];
        kp->state[index] = n;
        uint32_t input = 0;
        for (uint32_t i = 1; i <= index; ++i) {
            input *= 10;
            input += kp->state[i];
        }
        if (index == 4) {
            if(kp->state[5] == 0) {
                kp->pin = input;
                kp->state[5] = 1;
            } else if (kp->pin == input) {
                kp->state[5] = 0;
            } else {
                kp->state[5] += 1;
            }
            kp->state[0] = 0;
        }
    }
}
// cancel_key(&kp) modifies the state of the keypad `kp` as though the cancel key had been pressed
void cancel_key(keypad *kp) {
    if (kp->state[5] == 5) {
        kp->state[5] = 1;
    } else {
        kp->state[0] = 0;
    }
}
// cancel_key(&kp) modifies the state of the keypad `kp` as though the accept key had been pressed
void accept_key(keypad *kp) {
    if (kp->state[5] == 0) {
        kp->state[5] = 5;
        kp->state[0] = 0;
    }
}

// is_open(&kp) returns `true` if the door is the Open state, and `false` otherwise
bool is_open(keypad *kp) {
    return kp->state[5] >= 5;
}

int main(int argc, char* argv[]) {
    uint32_t pin = 0;
    char *c = argv[1];
// recovers the PIN as a decimal number from the first argument
    while (*c) {
        pin *= 10;
        pin += *c - 48;
        c++;
    }
// creates a new keypad with the input PIN
    keypad kp = new_keypad(pin);
    c = argv[2];
// calls the corresponding function for each input character in the second argument
    while (*c) {
        if (*c == 65) {
            accept_key(&kp);
        } else if (*c == 67) {
            cancel_key(&kp);
        } else {
            digit_key(&kp, *c - 48);
        }
        ++c;
    }
// tests if the door is open after receiving the input
    if (is_open(&kp)) {
        printf("door is open\n");
        exit(0);
    } else {
        printf("door is closed\n");
        exit(1);
    }
}
