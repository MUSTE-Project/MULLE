ROOT=`stack path --local-install-root`
# TODO Automatically figure out.
GHC=x86_64-linux-ghc-8.4.3
MUSTE_AJAX=muste-ajax-0.2.0.1
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
