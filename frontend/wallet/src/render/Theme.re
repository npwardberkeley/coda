/** Shared styles and colors */
open Css;

global("*", [boxSizing(`borderBox)]);

module Colors = {
  let string =
    fun
    | `rgb(r, g, b) => Printf.sprintf("rgb(%d,%d,%d)", r, g, b)
    | `rgba(r, g, b, a) => Printf.sprintf("rgba(%d,%d,%d,%f)", r, g, b, a)
    | `hsl(h, s, l) => Printf.sprintf("hsl(%d,%d%%,%d%%)", h, s, l)
    | `hex(s) => Printf.sprintf("#%s", s)
    | `hsla(h, s, l, a) =>
      Printf.sprintf("hsla(%d,%d%%,%d%%,%f)", h, s, l, a);

  let bgColor = white;

  let bgColorElectronWindow = "#00E9E9E9";

  let savilleAlpha = a => `rgba((61, 88, 120, a));
  let saville = savilleAlpha(1.);

  let hyperlinkAlpha = a => `rgba((45, 158, 219, a));

  let slateAlpha = a => `rgba((81, 102, 121, a));
  let slate = slateAlpha(1.);

  let roseBudAlpha = a => `rgba((163, 83, 112, a));
  let roseBud = roseBudAlpha(1.);

  let pendingOrange = `hex("967103");
  let greenblack = `hex("2a3c2e");

  let serpentine = `hex("479056");
  let serpentineLight = `rgba((101, 144, 110, 0.2));

  let yeezyAlpha = a => `rgba((197, 49, 49, a));
  let yeezy = yeezyAlpha(1.0);

  let clover = `rgb((71, 144, 86));

  let amberAlpha = a => `rgba((242, 149, 68, a));

  let mossAlpha = a => `rgba((101, 144, 110, a));

  let clay = `rgb((150, 113, 3));

  let marineAlpha = a => `rgba((51, 104, 151, a));
  let marine = marineAlpha(1.0);

  let midnightAlpha = a => `rgba((31, 45, 61, a));
  let midnight = midnightAlpha(1.0);

  let jungle = `hex("2BAC46");
  let sage = `hex("65906e");
  let blanco = `hex("e3e0d5");
  let modalDisableBgAlpha = a => `rgba((31, 45, 61, a));

  let headerBgColor = white;
  let headerGreyText = `hex("516679");
  let textColor = white;
  let borderColor = rgba(0, 0, 0, 0.15);

  // TODO: Rename
  let greyish = a => `rgba((51, 66, 79, a));

  let tealAlpha = a => `rgba((71, 130, 160, a));
  let teal = tealAlpha(1.0);
};

module Typeface = {
  // fontFace has the sideEffect of loading the font
  let _ = {
    [
      fontFace(
        ~fontFamily="IBM Plex Sans",
        ~src=[
          `url("fonts/IBMPlexSans-SemiBold-Latin1.woff2"),
          `url("fonts/IBMPlexSans-SemiBold-Latin1.woff"),
        ],
        ~fontStyle=`normal,
        ~fontWeight=`semiBold,
        (),
      ),
      fontFace(
        ~fontFamily="IBM Plex Sans",
        ~src=[
          `url("fonts/IBMPlexSans-Medium-Latin1.woff2"),
          `url("fonts/IBMPlexSans-Medium-Latin1.woff"),
        ],
        ~fontStyle=`normal,
        ~fontWeight=`medium,
        (),
      ),
      fontFace(
        ~fontFamily="IBM Plex Sans",
        ~src=[
          `url("fonts/IBMPlexSans-Regular-Latin1.woff2"),
          `url("fonts/IBMPlexSans-Regular-Latin1.woff"),
        ],
        ~fontStyle=`normal,
        ~fontWeight=`normal,
        (),
      ),
      fontFace(
        ~fontFamily="OCR A Std",
        ~src=[`url("fonts/OCR A Std Regular.ttf")],
        ~fontStyle=`normal,
        ~fontWeight=`normal,
        (),
      ),
    ];
  };

  let lucidaGrande = fontFamily("LucidaGrande");
  let plex = fontFamily("IBM Plex Sans, Sans-Serif");
  let mono = fontFamily("OCR A Std, monospace");
};

module Text = {
  module Body = {
    let regular =
      style([
        Typeface.plex,
        fontWeight(`medium),
        fontSize(`rem(1.)),
        lineHeight(`rem(1.5)),
      ]);

    let mono =
      style([
        Typeface.mono,
        fontWeight(`medium),
        fontSize(`rem(0.9)),
        // Due to the font weirdness, we need to offset by 4px
        paddingTop(`px(4)),
      ]);

    let small =
      style([
        Typeface.plex,
        fontWeight(`normal),
        fontSize(`rem(0.8125)),
        lineHeight(`rem(1.25)),
      ]);

    let semiBold =
      style([
        Typeface.plex,
        fontWeight(`semiBold),
        fontSize(`rem(1.)),
        lineHeight(`rem(1.5)),
        letterSpacing(`rem(-0.0125)),
      ]);
  };

  module Header = {
    let h3 =
      style([
        Typeface.plex,
        fontWeight(`medium),
        fontSize(`rem(1.25)),
        lineHeight(`rem(1.5)),
        letterSpacing(`rem(-0.03125)),
      ]);

    let h6 =
      style([
        Typeface.plex,
        fontWeight(`medium),
        fontSize(`rem(0.75)),
        lineHeight(`rem(1.0)),
        letterSpacing(`rem(0.0875)),
      ]);
  };

  let title =
    style([
      Typeface.plex,
      fontWeight(`normal),
      fontSize(`rem(2.25)),
      lineHeight(`rem(3.)),
    ]);
};

module CssElectron = {
  let appRegion =
    fun
    | `drag => `declaration(("-webkit-app-region", "drag"))
    | `noDrag => `declaration(("-webkit-app-region", "no-drag"));
};

module Spacing = {
  let defaultSpacing = `rem(1.);
  let defaultPadding = padding(defaultSpacing);
  let headerHeight = `rem(5.);
  let footerHeight = `rem(5.);
  let modalWidth = `rem(30.);
};

let notText = style([cursor(`default), userSelect(`none)]);

let codaLogoCurrent =
  style([
    width(`px(20)),
    height(`px(20)),
    backgroundColor(`hex("516679")),
    margin(`em(0.5)),
  ]);
