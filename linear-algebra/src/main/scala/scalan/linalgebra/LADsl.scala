package scalan.linalgebra

import scalan.{ScalanDsl, ScalanDslSeq, ScalanDslExp}

/**
 * Created by Victor Smirnov on 12/25/15.
 */

trait LADsl extends ScalanDsl
                with MatricesDsl with VectorsDsl

trait LADslSeq extends ScalanDslSeq
                with LADsl with MatricesDslSeq with VectorsDslSeq

trait LADslExp extends ScalanDslExp
                with LADsl with MatricesDslExp with VectorsDslExp
