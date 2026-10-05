package org.example

import io.github.oshai.kotlinlogging.KotlinLogging
import org.slf4j.LoggerFactory

private val logger = LoggerFactory.getLogger("Basic")
private val klogger = KotlinLogging.logger {}

class Worker(private val name: String) {
    fun run(count: Int) {
        logger.info("Worker {} starting", name)
        for (i in 0 until count) {
            logger.debug("$name processing item $i of ${count - 1}")
        }
        klogger.info { "Worker $name done" }
    }
}

fun main(args: Array<String>) {
    logger.info("Application starting with {} args", args.size)
    Worker("alpha").run(2)
}
