--////////////////////////////////////////////////////////////////////////////
--/  Copyright (C) by RivieraWaves.
--/  This module is a confidential and proprietary property of RivieraWaves
--/  and a possession or use of this module requires written permission
--/  from RivieraWaves.
--/---------------------------------------------------------------------------
--/ $Author: cvandebu $
--/ Company          : RivieraWaves
--/---------------------------------------------------------------------------
--/ $Revision: 2717 $
--/ $Date: 2010-05-25 15:16:31 +0200 (Tue, 25 May 2010) $
--/ --------------------------------------------------------------------------
--/ Dependencies     : None
--/ Description      : In-Band Power Estimator for MAXIM AGC Signal Processing 
--/ Application Note :
--/ Terms & concepts :
--/ Bugs             :
--/ Open issues and future enhancements :
--/ References       :
--/ Revision History :
--/ --------------------------------------------------------------------------
--/
--/ $HeadURL: https://svn.frso.rivierawaves.com/svn/rw/Projects/WLAN_IP_MAXIM/HW/SB/AGC/agc_sp/vhdl/rtl/inbd_power_est.vhd $
--/
--////////////////////////////////////////////////////////////////////////////


--------------------------------------------------------------------------------
-- Library
--------------------------------------------------------------------------------
  library ieee;
  use ieee.std_logic_1164.all;
  use ieee.std_logic_unsigned.all;
  use ieee.std_logic_arith.all;

  library std;
  use std.textio.all;

  library commonlib;
  use work.mdm_math_func_pkg.all;

  -- library agc_sp_rtl;
  -- use work.agc_sp_pkg.all;

--------------------------------------------------------------------------------
-- Entity
--------------------------------------------------------------------------------
  entity cca_detect is
  generic (
    data_in_g       : integer := 16;
    data_est_size_g : integer := 11
  );
  port(
    ---------------------------------
    -- Inputs Declaration
    ---------------------------------
    clk             :  in std_logic;                              -- Clock (60 MHz)
    reset_n         :  in std_logic;                              -- Reset (active LOW)
    en_20m_i        :  in std_logic;                              -- 20 MHz data enable input
    agc_inbd_pow_en :  in std_logic;                              -- Enable from AGC FSM
    modem_rx_a_i_rf :  in std_logic_vector(data_in_g-1 downto 0); -- Current i sample
    modem_rx_a_q_rf :  in std_logic_vector(data_in_g-1 downto 0); -- Current i sample
    reg_top_limit   :  in std_logic_vector(15 downto 0); 
    reg_lower_limit :  in std_logic_vector(15 downto 0); 
    ---------------------------------
    -- Outputs Declaration
    ---------------------------------
    cca_detect_o        : out std_logic
  );
  end entity cca_detect;  
  
---------------------------------------------------
-- Architecture
---------------------------------------------------
  architecture RTL of cca_detect is

  ---------------- Constants Declaration ---------------------------
  constant zeros_ct   : std_logic_vector(31 downto 0) := (others => '0');
  constant ones_ct    : std_logic_vector(31 downto 0) := (others => '1');
  ------------------------------------------------------------------
  type delay_line_type is array (31 downto 0) of std_logic_vector(data_est_size_g-1 downto 0);
  signal i_inbd_ff           : delay_line_type;
  signal q_inbd_ff           : delay_line_type;
  
          
  signal  i_inbd             : std_logic_vector(data_est_size_g-1 downto 0);      -- Current i sample
  signal  q_inbd             : std_logic_vector(data_est_size_g-1 downto 0);      -- Current q sample
  signal  i_inbd_ff32        : std_logic_vector(data_est_size_g-1 downto 0);      -- 1D i sample
  signal  q_inbd_ff32        : std_logic_vector(data_est_size_g-1 downto 0);      -- 1D q sample
  ----------------- Signals Declaration ------------------------------
  signal mult_pow_i          : std_logic_vector(2*data_est_size_g-1 downto 0);
  signal mult_pow_q          : std_logic_vector(2*data_est_size_g-1 downto 0);
  signal mult_pow_ff32_i     : std_logic_vector(2*data_est_size_g-1 downto 0);
  signal mult_pow_ff32_q     : std_logic_vector(2*data_est_size_g-1 downto 0);
  signal add_pow_int         : std_logic_vector(16 downto 0);
  signal add_pow_ff32_int    : std_logic_vector(16 downto 0);
  signal add_pow             : std_logic_vector(2*data_est_size_g downto 0);
  signal add_pow_ff32        : std_logic_vector(2*data_est_size_g downto 0);
  signal inbd_pow            : std_logic_vector(2*data_est_size_g downto 0);
  signal inbd_pow_ff         : std_logic_vector(2*data_est_size_g downto 0);
  
  signal cca_detect          : std_logic;
  signal TOP_LIMIT           : std_logic_vector(2*data_est_size_g downto 0);
  signal LOW_LIMIT           : std_logic_vector(2*data_est_size_g downto 0);
  
  /***********************************************************
  * ILA Debug
  ***********************************************************/
  attribute mark_debug:string;
  attribute mark_debug of inbd_pow_ff:signal is "true";
  attribute mark_debug of TOP_LIMIT:signal is "true";
  attribute mark_debug of LOW_LIMIT:signal is "true";
  attribute mark_debug of cca_detect:signal is "true";
    
  ------------------------------------
  -- Arcitecture Body
  ------------------------------------
  begin
  
   -- Delay line
    delay_line_p: process(reset_n, clk)
    begin
      if (reset_n = '0') then
        i_inbd_ff <= (others => (others => '0'));  
        q_inbd_ff <= (others => (others => '0'));  
      elsif (clk'event and clk = '1') then
        if (agc_inbd_pow_en = '1') then
          if (en_20m_i = '1') then
            --i_inbd_ff <= i_inbd_ff(i_inbd_ff'left - 1 downto 0) & modem_rx_a_i_rf[11:1];
            --q_inbd_ff <= q_inbd_ff(q_inbd_ff'left - 1 downto 0) & modem_rx_a_q_rf[11:1];
            i_inbd_ff <= i_inbd_ff(i_inbd_ff'left - 1 downto 0) & modem_rx_a_i_rf(11 downto 1);
            q_inbd_ff <= q_inbd_ff(q_inbd_ff'left - 1 downto 0) & modem_rx_a_q_rf(11 downto 1);
          end if;
        else
          i_inbd_ff <= (others => (others => '0'));
          q_inbd_ff <= (others => (others => '0'));
        end if;
      end if;
    end process delay_line_p;
    
    -- Outputs assignment 
    i_inbd      <= modem_rx_a_i_rf(11 downto 1);
    q_inbd      <= modem_rx_a_q_rf(11 downto 1);

    i_inbd_ff32  <= i_inbd_ff(31);
    q_inbd_ff32  <= q_inbd_ff(31);
  
  -- power_est
    TOP_LIMIT <= sxt(reg_top_limit,2*data_est_size_g+1);
    LOW_LIMIT <= sxt(reg_lower_limit,2*data_est_size_g+1);

    -- Square modulus
    mult_pow_i      <= signed(i_inbd) * signed(i_inbd);
    mult_pow_q      <= signed(q_inbd) * signed(q_inbd);
    add_pow         <= sxt(mult_pow_i, 2*data_est_size_g+1) + sxt(mult_pow_q, 2*data_est_size_g+1);

    mult_pow_ff32_i <= signed(i_inbd_ff32) * signed(i_inbd_ff32); 
    mult_pow_ff32_q <= signed(q_inbd_ff32) * signed(q_inbd_ff32); 
    add_pow_ff32    <= sxt(mult_pow_ff32_i, 2*data_est_size_g+1) + sxt(mult_pow_ff32_q, 2*data_est_size_g+1);

    -- Rounding and saturation
    add_pow_int      <= sat_round_unsigned_slv(add_pow,2,4);
    add_pow_ff32_int <= sat_round_unsigned_slv(add_pow_ff32,2,4);

    -- Inbd power estimate
    inbd_pow <= ((zeros_ct(5 downto 0) & add_pow_int) - (zeros_ct(5 downto 0) & add_pow_ff32_int)) + inbd_pow_ff;
   
    -- Register inbd power estimate
    inbd_pow_ff_p: process (reset_n, clk)
    begin
      if (reset_n = '0') then
        inbd_pow_ff <= (others => '0');
      elsif (clk'event and clk = '1') then
        if (agc_inbd_pow_en = '1') then
          if (en_20m_i = '1') then
            inbd_pow_ff <= inbd_pow;
          end if;
        else
          inbd_pow_ff <= (others => '0');
        end if;
      end if;
    end process inbd_pow_ff_p;


    agc_fall_d: process (reset_n, clk)
    begin
      if (reset_n = '0') then
        cca_detect <= '1';
      elsif (clk'event and clk = '1') then
        if (cca_detect = '1') then 
          if(inbd_pow_ff > TOP_LIMIT) then --fault is 1100
            cca_detect <= '0';
          else
            cca_detect <= '1';
          end if;
        else
          if(inbd_pow_ff < LOW_LIMIT) then --fault is 800
            cca_detect <= '1';
          else
            cca_detect <= '0';
          end if;
        end if;
      end if;
    end process agc_fall_d;

    -- Output assignment
    cca_detect_o    <= cca_detect;
    
  end architecture RTL;

--------------------------------------------------------
-- End of file
--------------------------------------------------------

