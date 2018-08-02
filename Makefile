# These three lines are horribly brittle.
ROOT := $(shell stack path --local-install-root)
GHC := x86_64-linux-$(shell stack query compiler actual)
MUSTE_AJAX := muste-ajax-$(shell stack query locals muste-ajax version | tr -d "'")

SHARE=${ROOT}/share
MUSTE_AJAX_SHARE=${SHARE}/${GHC}/${MUSTE_AJAX}
LOG=${MUSTE_AJAX_SHARE}/log
ACCESS_LOG=${LOG}/access.log
ERROR_LOG=${LOG}/error.log
PAGER=less -SF +F

log/error:
	${PAGER} ${ERROR_LOG}

log/access:
	${PAGER} ${ACCESS_LOG}
