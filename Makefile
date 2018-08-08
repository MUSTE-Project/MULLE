#################################################################
# This Makefile is mostly intended as a reminder about the long #
# convuluted commands we need.                                  #
#################################################################

# These three lines are horribly brittle.
ROOT := $(shell stack path --local-install-root)
GHC := x86_64-linux-$(shell stack query compiler actual)
MUSTE_AJAX := muste-ajax-$(shell stack query locals muste-ajax version | tr -d "'")
SHARE=${ROOT}/share
MUSTE_AJAX_SHARE=${SHARE}/${GHC}/${MUSTE_AJAX}
LOG=${MUSTE_AJAX_SHARE}/log

ACCESS_LOG=${LOG}/access.log
ERROR_LOG=${LOG}/error.log
DATABASE=${MUSTE_AJAX_SHARE}/data/muste.db

PAGER=less -SF +F
SQL=sqlite3

.PHONE: log/error log/access database ghcid

log/error:
	${PAGER} ${ERROR_LOG}

log/access:
	${PAGER} ${ACCESS_LOG}

database:
	${SQL} ${DATABASE}

ghcid:
	ghcid -c "stack ghci --test --ghci-options=-fno-break-on-exception --ghci-options=-fno-break-on-error --ghci-options=-v1 --ghci-options=-ferror-spans --ghci-options=-j"

hacky-sack/deploy/cse-principia:
	make -C muste-ajax hacky-sack/deploy/cse-principia
