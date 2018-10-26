`define RW_MAC_AC
// Define for 802.11ac support
`ifdef RW_MAC_AC
`define RW_TXTIME_DIVIDER_ONECYCLE
`define RW_MPDU_AC
`define RW_AES_AC
`define MPIFTXADDRWIDTH 7
`define MPIFRXADDRWIDTH 7
`ifndef WEP_2_BB_CLK_RATIO
  `define WEP_2_BB_CLK_RATIO 1
  `define NO_PRNG_FASTER_CLK
`endif
/*
`ifndef MAC_FREQ
  `define MAC_FREQ         200
`endif
`ifndef MACCORE_CLK_FREQ
  `define MACCORE_CLK_FREQ 200
`endif
`ifndef MACPI_CLK_FREQ
  `define MACPI_CLK_FREQ   250
`endif
`ifndef MPIF_CLK_FREQ
  `define MPIF_CLK_FREQ    180
`endif
*/
`endif

// Encryption support
// edit by fengmaoqiao
`define ENCRYPTION 1
//`define ENCRYPTION 0    // by mt
`define RX_BUFFER_ADDR_WIDTH 7
`define WEP                  1
`define TKIP                 1
`define CCMP                 1
`define RX_BUFFER_SIZE       128
`define DOT11I_SUPPORTED     1

// Indicates the clock ration between WEP Clock and MAC Core Clock
`ifndef WEP_2_BB_CLK_RATIO
  `define WEP_2_BB_CLK_RATIO 3
`endif

// Indicates if the WEP clock run faster than MAC Core Clock
`ifndef NO_PRNG_FASTER_CLK
  `define PRNG_FASTER_CLK    1
`endif

// Registers version
`define MACHW_SIGNATURE 6

`define RW_WLAN_COEX_EN
`ifdef RW_WLAN_COEX_EN
  `define MACHW_COEX      1
`else // RW_WLAN_COEX_EN
  `define MACHW_COEX      0
`endif //RW_WLAN_COEX_EN

`ifdef RW_WAPI_EN
  `define MACHW_WAPI      1
`else // RW_WAPI_EN
  `define MACHW_WAPI      0
`endif //RW_WAPI_EN

`define MACHW_TPC       1
`define MACHW_VHT       1        
`define MACHW_HT        1        
`define MACHW_RCE       1       
`define MACHW_CCMP      1      
`define MACHW_TKIP      1      
`define MACHW_WEP       1        
`define MACHW_SECURITY  1
`define MACHW_SME       1 
`define MACHW_HCCA      0      
`define MACHW_EDCA      1     
`define MACHW_QOS       1     

`define MACHW_PHASENUMBER   3   
`define MACHW_RELEASENUMBER 46
`define MACHW_IERELEASE     1      
`ifdef RW_THD_V2
// 37 = 0x25 = 2.05
 `define MACHW_UMVERSION     37
`else // RW_THD_V2
// 38 = 0x26 = 2.06
 `define MACHW_UMVERSION     38
`endif // RW_THD_V2


`define MACHW_BITMAPCNT 1


// MAC-PHY IF FIFOs configuration
`ifndef MPIFTXADDRWIDTH
  `define MPIFTXADDRWIDTH 6
`endif  
`ifndef MPIFRXADDRWIDTH
  `define MPIFRXADDRWIDTH 6
`endif  


// TX FIFOs configuration
`define TXFIFOADDRWIDTH 6
`define TXFIFODEPTH 64
`define TXFIFO_ALMOST_EMPTY_THRESHOLD 8
`define TXFIFO_ALMOST_FULL_THRESHOLD 4

// RX FIFOs configuration
`define RXFIFOADDRWIDTH 6
`define RXFIFODEPTH 64

// Key Storage RAM configuration
`define KEY_INDEX_WIDTH 6

// DOZE Controller Definition
// Number of fast clock cycles required to switch to Low Power Clock
`define SWITCHTO32K_DURATION 2
// Number of Low Power clock cycles required to switch to Fast Clock
`define SWITCHTOFASTCLK_DURATION 5
// Size of the DOZE counter
`define DOZECOUNTERSIZE 3  // Should be enough to count up to the max of SWITCHTO32K_DURATION and SWITCHTOFASTCLK_DURATION


// mac Registers defines
`ifndef MAC_FREQ
  `define MAC_FREQ                    80     // in MHz
`endif


// Timing definition.
// All these defines are the reset values of registers timings1-9.
// They can be changed here or by the software.
`define TX_RF_DLY                      1     // in us
`define TX_CHAIN_DLY                   2     // in us
`define TX_DMA_PROC_DLY                1     // in us

`define SHORT_SLOT                     9     // in us
`define MAC_PROC_DELAY                 5     // in us
`define TX_DLY_RF_ON                   1     // in us
`define RX_RF_DLY                      1     // in us
`define RX_CCA_DLY                     4     // in us

`define SIFS_A                        16     // in us
`define SIFS_B                        10     // in us


`define RIFS                           2     // in us
`define RIFSTO                         5     // in us
`define RX_DELAY_A                    10     // in us
`define RX_DELAY_B                    10     // in us

`define NO_BCN_TX_TIME                27     // in 16 us
`define IMP_TBTT_TIME                 26
`define RADIOWAKEUP_TIME              21
`define RADIO_CHIRP_TIME              20



`define SLOT_TIME_DOT11B              20     // used for 802.11 b data rates

`define SIFS_TIME_DOT11B              10     // used for 802.11 b data rates
`define SIFS_TIME_DOT11A              16     // used for 802.11 a data rates

`define EIFS_MINUS_DIFS_DOT11B       314
`define EIFS_MINUS_DIFS_DOT11A        60     // at PHY's lowest rate


// Configuration of the divider architecture. Depending on the clock frequency, two architectures are available.
// For high macCoreClk frequency (above 100MHz), it is recommended to use RW_TXTIME_DIVIDER_ONECYCLE.
// For low macCoreClk frequency (below 80MHz), it is recommended to use RW_TXTIME_DIVIDER_FIVECYCLE.

// With this define, the divider computes 1 step per clock cycles.
// The max frequency in FPGA Virtex 5 is ~130MHz.
//`define RW_TXTIME_DIVIDER_ONECYCLE

// With this define, the divider computes 5 steps per clock cycles.
// The max frequency in FPGA Virtex 5 is ~45MHz.
`ifndef RW_TXTIME_DIVIDER_ONECYCLE
  `define RW_TXTIME_DIVIDER_FIVECYCLE
`endif  

// Number of Spatial Stream supported
// Note : If the MAC Support 3SS, both defines RW_MAC_2SS_SUPPORT and RW_MAC_3SS_SUPPORT shall be present. Only the define RW_MAC_4SS_SUPPORT shall be commented.
`ifndef RW_1NSS_ONLY
  `define RW_MAC_2SS_SUPPORT
  `define RW_MAC_3SS_SUPPORT
  `define RW_MAC_4SS_SUPPORT
`endif

// Support MIB Controller
// If the MIB Controller is not required, the following line can be commented.
//modedified by fengmaoqiao
`define RW_MAC_MIBCNTL_EN
