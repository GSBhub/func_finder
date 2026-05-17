import argparse
import json
import logging
import sys

from . import parse_rom


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Extract function feature vectors from M7700 ECU binaries."
    )
    parser.add_argument("files", nargs="+", metavar="FILE", help="M7700 ROM file(s)")
    parser.add_argument("-o", "--output", default="file.json", metavar="FILE",
                        help="Output JSON path (default: file.json)")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.WARNING)

    results: dict = {}
    for path in args.files:
        print(f"Opening: {path}")
        results[path] = parse_rom(path)

    with open(args.output, "w") as fh:
        json.dump(results, fh, indent=4, sort_keys=True)
    print(f"Wrote results to {args.output}")


if __name__ == "__main__":
    main()
