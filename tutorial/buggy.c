#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    // stored PIN as a u32
    uint32_t pin;
    // current input as a u32
    uint32_t input;
    // number of read digits
    uint8_t nread;
    // keypad state:
    //  0: unlocked
    //  1: locked, 0 attempts
    //  2: locked, 1 attempts
    //  3: locked, 2 attempts
    //  4: blocked
    //  5: open
    uint8_t state;
} keypad;

keypad new_keypad(uint32_t pin) {
    keypad kp = {pin, 0, 0, 1};
    return kp;
}

void digit_key(keypad *kp, uint8_t n) {
    // if the door is either locked or unlocked
    if (kp->state <= 4) {
        // read the digit
        kp->nread += 1;
        kp->input *= 10;
        kp->input += n;
        // if four digits have been read
        if (kp->nread == 4) {
            // if the door is unlocked
            if (kp->state == 0) {
                // set the current PIN as the stored PIN
                kp->pin = kp->input;
                // reset input state
                kp->input = 0;
                kp->nread = 0;
                // set door state to locked, 0 attempts
                kp->state += 1;
            } else if (kp->pin == kp->input) {
                // if the door is not unlocked and stored PIN and the input coincide
                // reset input state
                kp->input = 0;
                kp->nread = 0;
                // set door to unlocked
                kp->state = 0;
            } else {
                // if the door is not unlocked and store PIN and input do not coincide
                // reset input state
                kp->input = 0;
                kp->nread = 0;
                // set door to locked +1 attempt, or blocked if 2 attempts
                kp->state += 1;
            }
        }
    }
}
void cancel_key(keypad *kp) {
    // if the door is open
    if (kp->state == 5) {
        // set the door to locked, 0 attempts
        kp->state = 1;
    } else {
        // reset input state
        kp->nread = 0;
        kp->input = 0;
    }
}
void accept_key(keypad *kp) {
    // if the door is unlocked
    if (kp->state == 0) {
        // reset the input state
        kp->input = 0;
        kp->nread = 0;
        // set the door to open
        kp->state = 5;
    }
}

bool is_open(keypad *kp) {
    return kp->state == 5;
}

int main(int argc, char* argv[]) {
    uint32_t pin = 0;
    char *c = argv[1];
    while (*c) {
        pin *= 10;
        pin += *c - 48;
        c++;
    }
    keypad kp = new_keypad(pin);
    c = argv[2];
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
    if (is_open(&kp)) {
        printf("door is open\n");
        exit(0);
    } else {
        printf("door is closed\n");
        exit(1);
    }
}