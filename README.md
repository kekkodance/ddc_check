
<p align="center">
  <img src="icon.ico" alt="App Icon" width="100">
</p>

<h1 align="center">ddc_check</h1>


This program is meant for people using multiple monitors, especially artists with drawing tablets that have screens. Its purpose is to handle a common issue where Windows still treats a monitor as active even when it’s turned off.

When a monitor is detected as off through the DDC/CI protocol, the program will effectively “detach” it (without actually disabling DDC/CI). It then moves any open windows to another monitor, prevents new windows from appearing on the "detached" screen, and stops the mouse cursor from moving into that area.

## Notes

* Administrator privileges are required. This is necessary to move elevated windows and restrict cursor movement.
* The primary monitor is never "detached", even if it appears to be off.
* It works best when monitors are different models.
* There may be issues with identical monitors due to EDID conflicts.

## Download

The program is available in the [**Releases**](https://github.com/kekkodance/ddc_check/releases/latest) section.
