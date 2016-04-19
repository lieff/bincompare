#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <math.h>
#include <memory.h>
#include <windows.h>

#include "conio3.h"

#ifndef MAX
#   define MAX( x, y )          ( (x)>(y)?(x):(y) )
#endif

#ifndef MIN
#   define MIN( x, y )          ( (x)<(y)?(x):(y) )
#endif

#ifndef ABS
#   define ABS( x )             ( (x)>=0?(x):-(x) )
#endif

#define ATR_DEF 7
#define ATR_DIF 4
#define ATR_MAGENTA 13
#define ATR_YELLOW 14

#define STICKY_ALIGN 1

static int getKeyWin32(void)
{
    INPUT_RECORD buf;
    unsigned long numRead;
    SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), 0); 
    if (WaitForSingleObject(GetStdHandle(STD_INPUT_HANDLE),0) != WAIT_OBJECT_0)
    {
        return 0;
    }
    if (! ReadConsoleInput(
        GetStdHandle(STD_INPUT_HANDLE), // input buffer handle
        &buf,                           // buffer to read into
        1,                              // size of read buffer
        &numRead) )                     // number of records read
    {
        return 0;
    }
    if (buf.EventType == KEY_EVENT && buf.Event.KeyEvent.bKeyDown)
    {
        return buf.Event.KeyEvent.wVirtualKeyCode;
    }
    return 0;
} 


static int escPressed(void)
{
    return (getKeyWin32() == 27);
}

static int waitKeyWin32(int * ctrl)
{
    INPUT_RECORD buf;
    unsigned long numRead;
    SetConsoleMode(GetStdHandle(STD_INPUT_HANDLE), 0); 
    for (;;)
    {
        if (WaitForSingleObject(GetStdHandle(STD_INPUT_HANDLE),INFINITE) != WAIT_OBJECT_0)
        {
            return 0;
        }
        if (ReadConsoleInput(
            GetStdHandle(STD_INPUT_HANDLE), // input buffer handle
            &buf,                           // buffer to read into
            1,                              // size of read buffer
            &numRead) )                     // number of records read
        {
            if (buf.EventType == KEY_EVENT && buf.Event.KeyEvent.bKeyDown)
            {
                *ctrl = !!(buf.Event.KeyEvent.dwControlKeyState & (LEFT_CTRL_PRESSED | RIGHT_CTRL_PRESSED));
                return buf.Event.KeyEvent.wVirtualKeyCode;
            }
        }
    }
} 

struct text_info console_info;
struct __char_info * backbuf;
int max_page_chars;
int column_chars;
int page_lines;
int * buf[2];
int cur_page_chars[2];  
int buf_size;
int g_align;
int pos[2] = {0,0};
int maxpos[2] = {0,0};
size_t file_bytes[2] = {0,0};
FILE * f[2];
char * file_name[2];
enum 
{
    e_hex,
    e_bin
} mode = e_hex;

struct 
{
    int replace;
    int insert;
    int delete;
} edit_distance;


struct __char_info *  cpy(struct __char_info * dst, char * line, int attr)
{
    while(*line)
    {
        dst->letter = *line;
        dst->attr = attr;
        line++;
        dst++;
    }
    return dst;
}

int myfread(int * buf, int n, FILE * f, int pos, int max_pos)
{
    int i, j = 0;
    unsigned char * tmp = malloc(n);
    int  p = pos < 0?0:pos;
    if (p > max_pos) p = max_pos;
    fseek(f, p, SEEK_SET);
    fread(tmp, 1, n, f);
    if(mode == e_hex)    
    {
        for (i = 0; i < n; i++, pos++)
        {
            buf[i] = -1;
            if (pos >= p && pos < max_pos) 
                buf[i] = tmp[j++];
        }
    }
    else
    {
        int k = 7;
        for (i = 0; i < n; i++)
        {
            buf[i] = -1;
            if (pos >= p && pos < max_pos) buf[i] = (tmp[j]>>k)&1;
            if (--k < 0) k = 7, j++, pos++;
        }
    }
    free(tmp);
    return pos;
}

typedef int symbol_t;
#define SUB_COST 2
#define DEL_COST 1
#define INS_COST 1


// computes the Levenshtein distance between two strings
// "x" represent the pattern and "y" represent the text
// "m" is the pattern length and "n" is the text length
void align(symbol_t *x, unsigned int nx, symbol_t *y, unsigned int ny) 
{
    typedef struct
    {
#define OP_SUB 1
#define OP_INS 2
#define OP_DEL 4
        int op_flags;
    } cost_context_t;

    // complementary variables for computing the "Levenshtein distance"
    unsigned int i, j, k;
    symbol_t * ty = calloc(nx+ny+1, sizeof(symbol_t));
    symbol_t * tx = calloc(nx+ny+1, sizeof(symbol_t));
    int cut_flag = 0;

    int * matrix = calloc((nx+1)*(ny+1), sizeof(int));
    cost_context_t * ctx = calloc((ny+1), sizeof(cost_context_t));

    int stride = ny+1;
    if (!nx || !ny) 
    {
        return;
    } 

    for(i = 0; i <= ny; ++i) {
        matrix[0*stride + i] = i; 
    }
    for(i = 0; i <= nx; ++i) {
        matrix[i*stride + 0] = i; 
    }

    // starting the main process for computing 
    // the distance between the two strings "x" and "y"
    for(i = 1; i <= nx; ++i) 
    {
        for(j = 1; j <= ny; ++j) 
        {
            int ins_cost = matrix[(i-1)*stride+j  ] + INS_COST;    // above
            int del_cost = matrix[(i  )*stride+j-1] + DEL_COST;    // left
            int sub_cost = matrix[(i-1)*stride+j-1] + SUB_COST*(x[i-1] != y[j-1]); // diagonal
//printf("%d %d %d\n", ins_cost, del_cost, sub_cost) ;
            if (!(ctx[j].op_flags & OP_INS)) ins_cost += 1;
            if (!(ctx[0].op_flags & OP_DEL)) del_cost += 1;
            if (sub_cost < ins_cost && sub_cost < del_cost)
            {
                matrix[i*stride+j] = sub_cost;
                ctx[j].op_flags = ctx[0].op_flags = OP_SUB;
            }
            else if (ins_cost < del_cost)
            {
                matrix[i*stride+j] = ins_cost;
                ctx[j].op_flags = ctx[0].op_flags = OP_INS;
            }
            else 
            {
                matrix[i*stride+j] = del_cost;
                ctx[j].op_flags = ctx[0].op_flags = OP_DEL;
            }
//            printf("%d ",matrix[i*stride+j]);

        }
//        printf("\n");
    }

    edit_distance.replace = 0;
    edit_distance.insert = 0;
    edit_distance.delete = 0;

    k = nx+ny; 
    tx[k] = ty[k] = 0;
    for (i = nx, j = ny; i > 0 && j > 0; )
    {
        int ed = matrix[(i)*stride+j];
        int ins_cost = matrix[(i-1)*stride+j];
        int del_cost = matrix[(i)*stride+j-1];
        int sub_cost = matrix[(i-1)*stride+j-1];
        k--;
        if (sub_cost <= ins_cost && sub_cost <= del_cost)
        {
            tx[k] = x[--i];
            ty[k] = y[--j];
            edit_distance.replace += tx[k]!=ty[k];
        }
        else if (ins_cost < del_cost)
        {
            tx[k] = x[--i];
            ty[k] = -1;
            edit_distance.insert++;
        }
        else
        {
            tx[k] = -1;
            ty[k] = y[--j];
            edit_distance.delete++;
        }
    }
    while(i > 0) 
    { 
        --k; tx[k] = x[--i]; ty[k] = -1; edit_distance.insert++;
    }
    while(j > 0) 
    { 
        --k; tx[k] = -1; ty[k] = y[--j]; edit_distance.delete++;
    }

    while (tx[k] < 0 && ty[k] < 0) {k++; pos[1]++;}

    memcpy(x,tx+k,max_page_chars*sizeof(symbol_t));
    memcpy(y,ty+k,max_page_chars*sizeof(symbol_t));

    cur_page_chars[0] = cur_page_chars[1] = 0;
    for (i = 0; i < MIN(max_page_chars,nx); i++)  cur_page_chars[0] += (x[i] >= 0);
    for (i = 0; i < MIN(max_page_chars,ny); i++)  cur_page_chars[1] += (y[i] >= 0);
    //assert(_CrtCheckMemory());

    free(tx);
    free(ty);
    free(matrix);
}


void make2(FILE * f[2])
{
    int i,j,r;
    char line[1000], *p = line;
    int cur_pos[2];
    int last_pos[2];
    struct __char_info * pb;
    for (i = 0; i < 2; i++)
    {
        cur_pos[i] = pos[i];
if (mode != e_hex) cur_pos[i] *= 8;
        last_pos[i] = myfread(buf[i], buf_size, f[i], pos[i], file_bytes[i]);
    }
    if (g_align)
    {
        align(buf[0],max_page_chars*1,buf[1],max_page_chars*1);
#if !STICKY_ALIGN
        g_align = 0;
#endif
    }

    // top line with file names
    pb = backbuf;
    sprintf(line, "          %-*s| %-*s Edit distance: %3d r:%3d i:%3d d:%3d", column_chars*3, file_name[0], 
                                          column_chars*5+3  -37, file_name[1], 
                                          edit_distance.replace + edit_distance.insert + edit_distance.delete,
                                          edit_distance.replace, edit_distance.insert, edit_distance.delete
                                          );
    pb = cpy(pb, line, 0 + (7<<4));


    // print offset info line
    pb = backbuf + console_info.screenwidth;
    memset(pb,0,sizeof(*pb)*console_info.screenwidth);
    if (pos[0] != pos[1])
    {
        if ((int)pos[0] > (int)pos[1]) 
            sprintf(line, "%d bytes moved right", pos[0] - pos[1]);
        else
            sprintf(line, "%d bytes moved left", pos[1] - pos[0]);
        pb = cpy(pb+column_chars*3+10+2, line, ATR_MAGENTA);
    }
        

    for (r = 0; r < page_lines; r++)
    {
        pb = backbuf + (r+2)*console_info.screenwidth;

        if (mode == e_hex)
        {
            sprintf(line, "%08X: ",  cur_pos[0]);
            pb = cpy(pb, line, ATR_DEF);
            for (j = 0; j < 2; j++)
            {
                if (cur_pos[j] >= file_bytes[j] && cur_pos[j] < file_bytes[j] + column_chars)
                {
                    sprintf(line, "%-*s", column_chars*3, "* * * End of file * * *"); 
                    pb = cpy(pb, line, ATR_YELLOW);
                    cur_pos[j] += column_chars;
                }
                else for (i = r*column_chars; i < (r+1)*column_chars; i++) 
                {
                    strcpy(line, "   "); 
                    if (buf[j][i] >= 0) 
                    {
                        sprintf(line, "%02X ", buf[j][i]); 
                        cur_pos[j]++;
                    }
                    pb = cpy(pb, line, buf[0][i]==buf[1][i]?ATR_DEF:ATR_DIF);
                }
                pb = cpy(pb, "| ", ATR_DEF);
            }

            for (i = 0; i < column_chars; i++)
            {
                int c0 = buf[0][r*column_chars + i];
                int c1 = buf[1][r*column_chars + i];
                pb->letter = c0;
                pb->attr = c0==c1?ATR_DEF:ATR_DIF;
                pb[column_chars+1].letter = c1;
                pb[column_chars+1].attr = c0==c1?ATR_DEF:ATR_DIF;
                pb++;
            }
            pb = cpy(pb, "|", ATR_DEF);
        }
        else
        {
            sprintf(line, "%08X:%d ", cur_pos[0]/8, cur_pos[0]%8);
            pb = cpy(pb, line, ATR_DEF);
            for (j = 0; j < 2; j++)
            {
                if (cur_pos[j]/8 >= file_bytes[j] && cur_pos[j]/8 < file_bytes[j] + column_chars/8)
                {
                    sprintf(line, "%-*s", column_chars*3, "* * * End of file * * *"); 
                    pb = cpy(pb, line, ATR_YELLOW);
                    cur_pos[j] += column_chars;
                }
                else for (i = r*column_chars; i < (r+1)*column_chars; i++) 
                {
                    strcpy(line, " "); 
                    if (buf[j][i] >= 0) 
                    {
                        sprintf(line, "%c", "\xfa\xfe"[buf[j][i]]); 
                        cur_pos[j]++;
                    }
                    pb = cpy(pb, line, buf[0][i]==buf[1][i]?ATR_DEF:ATR_DIF);
                }
                pb = cpy(pb, "|", ATR_DEF);
            }
        }
    }

    pb = backbuf + (r+2)*console_info.screenwidth;
    sprintf(line, "Keys: Esc,%c,%c,%c,%c,Ctrl+%c,Ctrl+%c,Home,End,PgUp,PgDn", 24, 25, 26, 27, 26, 27);
    pb = cpy(pb, line, 0 + (7<<4));


    puttext(1,1,console_info.screenwidth,console_info.screenheight,backbuf);
}


#define FILE_BUF_BYTES  0x4000
void seekdif()
{
    static unsigned char g_bytebuf[2][FILE_BUF_BYTES];
    int i, phase = 0;
    int delta = pos[1] - pos[0];
    fseek(f[0], pos[0], SEEK_SET);
    fseek(f[1], pos[1], SEEK_SET);
    while (!escPressed())
    {
        int samples[2];
        int samplesToCompare;

        samples[phase] = fread(g_bytebuf[phase], 1, FILE_BUF_BYTES, f[phase]);
        phase ^= 1;                                                         
        samples[phase] = fread(g_bytebuf[phase], 1, FILE_BUF_BYTES, f[phase]);
        
        samplesToCompare = MIN(samples[0], samples[1]);
        if (!samplesToCompare)
        {
            while (pos[0]%column_chars) pos[0]--;
            for (i = 0; i < page_lines/2; i++)
                if (pos[0] >= column_chars) pos[0] -= column_chars;

            break;
        }
        for (i = 0; i < samplesToCompare; i++)
        {
            if (g_bytebuf[0][i] != g_bytebuf[1][i])
            {
                pos[0] += i;

                while (pos[0]%column_chars) pos[0]--;
                if (pos[0] >= column_chars) pos[0] -= column_chars;

                goto exit;
            }
        }
        pos[0] += i;
    }
exit:

    pos[1] = pos[0] + delta;
}

int can_move(int dpos, int file)
{
    int max_pos = MAX(maxpos[0], maxpos[1]);
    if ((int)pos[file] < -dpos) return -pos[file];
    if ((int)pos[file] + dpos > (int)max_pos) return max_pos-pos[file];
    return dpos;
}

void advance(int nfile, int dpos)
{
    pos[nfile] += dpos;
}

int get_rowbytes(int nfile, int n, int nrow)
{
#if 1
    int i, j;
    for (i = nrow*n, j = 0; i < (nrow+1)*n; i++)
    {
        j += buf[nfile][i] >= 0;
    }
    return j;
    return j?j:n;
#else
    return n;
#endif
}

void set_column_chars(int arg_column_chars)
{
    column_chars = arg_column_chars;
    page_lines = console_info.screenheight;
    page_lines--; // top line with file names 
    page_lines--; // next line with offsets
    page_lines--; // bottom line

    max_page_chars = column_chars * page_lines;
}

static void help()
{
    int ctrl;
    clrscr();
    printf(
"   ASP bincompare\n"
"   ======================= Keys =======================\n"
"   Esc           Quit\n"
"   's'           Find next difference\n"
"   'b'           Toggle byte/bit mode\n"
"   'a'           Toggle data alignment\n"
"   '+'           Increase width\n"
"   '-'           Decrease width\n"
"   \x1A             Offset right by 1 symbol\n"
"   \x1B             Offset left by 1 symbol\n"
"   Ctrl+\x1A        Offset right by 1 row\n"
"   Ctrl+\x1B        Offset left by 1 row\n"
"   Numpad '5'    Reset offset\n"
"   \x18             Line up\n"
"   \x19             Line down\n"
"   PgDn          Screen down\n"
"   PgUp          Screen up\n"
"   Home          Move to beginning\n"
"   End           Move to end\n"
"   ====================================================\n"
"\n"
"   This software based on ideas from Randy Compare DOS utility\n"
"\n"
"   Press any key...\n"
    );
    waitKeyWin32(&ctrl);
}

int main(int argc, char* argv[])
{
    int i, need_update = 1;
    int symbols_per_byte = 3+1;
    int default_column_chars;
    gettextinfo(&console_info);

    if (argc != 3)
    {
        printf("Usage: Compare <file1> <file2>\n");
        return 1;
    }

    buf_size = console_info.screenwidth*console_info.screenheight;
    default_column_chars = (console_info.screenwidth-10-3-1)/2/symbols_per_byte;
    set_column_chars(default_column_chars);

    for (i = 0; i < 2; i++)
    {
        file_name[i] = argv[1+i];
        f[i] = fopen(argv[1+i], "rb");
        if (!f[i]) 
        {
            printf("ERROR: Can not open file %s\n", argv[1+i]);
            return 1;
        }
        fseek(f[i], 0, SEEK_END);
        file_bytes[i] = ftell(f[i]);
        maxpos[i] = ((file_bytes[i] - max_page_chars + column_chars + column_chars-1)/column_chars)*column_chars;
        rewind(f[i]);
        buf[i] = malloc(buf_size*sizeof(buf[0][0]));
        if (!buf[i])
        {
            printf("ERROR: Can not allocate %d bytes\n", buf_size);
            return 1;
        }
    }

    backbuf = malloc(sizeof(struct __char_info)*console_info.screenwidth*console_info.screenheight);

    clrscr();
    seekdif();
    for(;;)
    {
        int k,d0,d1,ctrl;
        cur_page_chars[0] = cur_page_chars[1] = max_page_chars;
        if (need_update)
        {
            make2(f);
        }
        need_update = 1;
        k = waitKeyWin32(&ctrl);
        switch(k)
        {
            case  0: // system error
            case 27: // escape
                return 0;
            case 39: // right
                d1 = (ctrl?-get_rowbytes(1,column_chars,page_lines-1):-1);
                d1 = -can_move(-d1,0);
                advance(1, d1); break;
            case 37: // left
                d1 = (ctrl?get_rowbytes(1,column_chars,0):+1);
                d1 = can_move(d1,1);
                advance(1, d1); break;
            case 38: // up 
                // how many symbols are need to be removed?
                d0 = get_rowbytes(0,column_chars,page_lines-1);
                d1 = get_rowbytes(1,column_chars,page_lines-1);
                if (pos[0]+cur_page_chars[0] >= file_bytes[0] || pos[1]+cur_page_chars[1] >= file_bytes[1])
                {
                    d0 = d1 = 0;   
                }
                if (!d0 && !d1) d0 = d1 = column_chars;

                d0 = can_move(-d0,0);
                d1 = can_move(-d1,1);
                advance(0, d0);
                advance(1, d1); break;
            case 40: // down
                d0 = get_rowbytes(0,column_chars,0);
                d1 = get_rowbytes(1,column_chars,0);
                //if (!d0 && !d1) d0 = d1 = column_chars;
                d0 = can_move(d0,0);
                d1 = can_move(d1,1);
                if (pos[0] >= file_bytes[0])
                {
                    d0 = d1;
                }
                if (pos[1] >= file_bytes[1])
                {
                    d1 = d0;
                }
                advance(0, d0); 
                advance(1, d1); break;

            case 33: // page up
                d0 = get_rowbytes(0,max_page_chars,0);
                d1 = get_rowbytes(0,max_page_chars,0);
                if (pos[0]+cur_page_chars[0] >= file_bytes[0] || pos[1]+cur_page_chars[1] >= file_bytes[1])
                {
                    d0 = d1 = 0;   
                }
                if (!d0 && !d1) d0 = d1 = max_page_chars;
                d0 = can_move(-d0,0);
                d1 = can_move(-d1,1);
                advance(0, d0); 
                advance(1, d1); break;
            case 34: // page down
                if (!cur_page_chars[0]) cur_page_chars[0] = cur_page_chars[1];
                if (!cur_page_chars[1]) cur_page_chars[1] = cur_page_chars[0];
                d0 = can_move(cur_page_chars[0],0);
                d1 = can_move(cur_page_chars[1],1);
                advance(0, d0); 
                advance(1, d1); break;
            case 36: // home
                pos[1] = pos[0] = 0;
                break;
            case 35: // end
                if (pos[0] < maxpos[0] && pos[1] < maxpos[1])
                    pos[1] = pos[0] = MIN(maxpos[0], maxpos[1]);
                else 
                    pos[1] = pos[0] = MAX(maxpos[0], maxpos[1]);
                break;
            case 12: // numlock '5'
                pos[1] = pos[0];
                set_column_chars(default_column_chars);
                need_update = 1;
                break;
            case 109: // numlock '-'
            case 189: // '-'
                if (column_chars > 1)
                {
                    set_column_chars(column_chars-1);
                    need_update = 1;
                    memset(backbuf,0,sizeof(struct __char_info)*console_info.screenwidth*console_info.screenheight);
                }
                break;
            case 107: // numlock '+'
            case 187: // '+'
                if (column_chars < default_column_chars)
                {
                    set_column_chars(column_chars+1);
                    need_update = 1;
                }
                break;
            case 112: // F1
                help();
                break;
            case 'a':
            case 'A':
                g_align = !g_align;
                break;
            case 's':
            case 'S':
                pos[0] += max_page_chars;
                pos[1] += max_page_chars;
                seekdif();
                break;
            case 'b':
            case 'B':
                memset(backbuf,0,sizeof(struct __char_info)*console_info.screenwidth*console_info.screenheight);
                if (mode == e_hex)
                {
                    mode = e_bin;
                    //symbols_per_byte = 9+1;
                    symbols_per_byte = 1;
                    default_column_chars = (console_info.screenwidth-10-3-1)/2/symbols_per_byte;
                    set_column_chars(default_column_chars);
                }
                else
                {
                    mode = e_hex;
                    symbols_per_byte = 3+1;
                    default_column_chars = (console_info.screenwidth-10-3-1)/2/symbols_per_byte;
                    set_column_chars(default_column_chars);
                }
                break;
            default: 
//printf("%d\n",k);
                need_update = 0;
        }
    }

//    printf("Hello World!\n");
    return 0;
}
