import Erdos883AdaptiveCertificate1840Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1840_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 10 18005362031760922492204538576256041990989307547299709200707774814021192903774328950652314418322946539175155029470880906662640735688918740163943426860653411323910558882509584713885065592054897266265764059576219078073364543146344698357165794719751493430315706906843027504398555838492576271889422352448
def adaptiveNumericSpans1840_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_0Chunk0].flatten
def adaptiveSpanEven1840_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_0)
def adaptiveSpanWhole1840_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_0)
theorem adaptiveSpanNumericCheck1840_0 : coreNumericSpansCheck 1796 6 480 1155 adaptiveNumericSpans1840_0 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_0 : adaptiveSpanEven1840_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_0 : adaptiveSpanEven1840_0.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_0 : adaptiveSpanEven1840_0.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_0 := by decide +kernel
theorem adaptiveSpanWholeCache1840_0 : adaptiveSpanWhole1840_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_0 : adaptiveSpanWhole1840_0.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_0 : adaptiveSpanWhole1840_0.spans = coreWholeSpans 0 adaptiveNumericSpans1840_0 := by decide +kernel
def adaptiveNumericSpans1840_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11204764300706914807837927142368310191901033112075861260560054529651468415080993419715754116919928395056275815941185726603748524405099001563962010871101480326302128287152461582501548016723279371691867666153656357762837705574004101885198464
def adaptiveNumericSpans1840_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_1Chunk0].flatten
def adaptiveSpanEven1840_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_1)
def adaptiveSpanWhole1840_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_1)
theorem adaptiveSpanNumericCheck1840_1 : coreNumericSpansCheck 1796 6 240 385 adaptiveNumericSpans1840_1 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_1 : adaptiveSpanEven1840_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_1 : adaptiveSpanEven1840_1.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_1 : adaptiveSpanEven1840_1.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_1 := by decide +kernel
theorem adaptiveSpanWholeCache1840_1 : adaptiveSpanWhole1840_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_1 : adaptiveSpanWhole1840_1.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_1 : adaptiveSpanWhole1840_1.spans = coreWholeSpans 0 adaptiveNumericSpans1840_1 := by decide +kernel
def adaptiveNumericSpans1840_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11204764300706914807837927142368310191901033112075861260560054529651468415080993419715754116919928395056275815941185726603748524405099001563962010871101608542510153408388445218171044009967814236394880324746619841359146095278468209049600128
def adaptiveNumericSpans1840_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_2Chunk0].flatten
def adaptiveSpanEven1840_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_2)
def adaptiveSpanWhole1840_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_2)
theorem adaptiveSpanNumericCheck1840_2 : coreNumericSpansCheck 1796 6 720 1001 adaptiveNumericSpans1840_2 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_2 : adaptiveSpanEven1840_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_2 : adaptiveSpanEven1840_2.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_2 : adaptiveSpanEven1840_2.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_2 := by decide +kernel
theorem adaptiveSpanWholeCache1840_2 : adaptiveSpanWhole1840_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_2 : adaptiveSpanWhole1840_2.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_2 : adaptiveSpanWhole1840_2.spans = coreWholeSpans 0 adaptiveNumericSpans1840_2 := by decide +kernel
def adaptiveNumericSpans1840_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28933501249492976339097310198254443930129926615801934791790285000657028150494724617139708617322671318278402244913581075788236246456046809855880874510525066381964691951807968315125410270675721083763400997629459123310650970719016965412262633647954823916209632391835967649058706239748499042404575727223820826552718614823769368973747625618938916427786746956087424
def adaptiveNumericSpans1840_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_3Chunk0].flatten
def adaptiveSpanEven1840_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_3)
def adaptiveSpanWhole1840_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_3)
theorem adaptiveSpanNumericCheck1840_3 : coreNumericSpansCheck 1796 6 120 143 adaptiveNumericSpans1840_3 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_3 : adaptiveSpanEven1840_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_3 : adaptiveSpanEven1840_3.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_3 : adaptiveSpanEven1840_3.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_3 := by decide +kernel
theorem adaptiveSpanWholeCache1840_3 : adaptiveSpanWhole1840_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_3 : adaptiveSpanWhole1840_3.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_3 : adaptiveSpanWhole1840_3.spans = coreWholeSpans 0 adaptiveNumericSpans1840_3 := by decide +kernel
def adaptiveNumericSpans1840_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28933501249492976339097310198254443930129926615801934791790285000657028150494724617139708617322671318278402244913581075788516047610133136380101338304219372939960022564241973659331544076450382536773240960584715235983862563748209607823593293326611515518477004148528056766840297577806024303867614434157574755453791546533010778242659144502400983146992238709440640
def adaptiveNumericSpans1840_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_4Chunk0].flatten
def adaptiveSpanEven1840_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_4)
def adaptiveSpanWhole1840_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_4)
theorem adaptiveSpanNumericCheck1840_4 : coreNumericSpansCheck 1796 6 192 221 adaptiveNumericSpans1840_4 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_4 : adaptiveSpanEven1840_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_4 : adaptiveSpanEven1840_4.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_4 : adaptiveSpanEven1840_4.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_4 := by decide +kernel
theorem adaptiveSpanWholeCache1840_4 : adaptiveSpanWhole1840_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_4 : adaptiveSpanWhole1840_4.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_4 : adaptiveSpanWhole1840_4.spans = coreWholeSpans 0 adaptiveNumericSpans1840_4 := by decide +kernel
def adaptiveNumericSpans1840_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 28933501249492976339097310198254443930129926615801934791790285000657028150494724617139708617362977007721153983129119398426120401323242967686285738167585102872161054087635165916145005961791363562588625092527567445157981613116868894870968647503759686615821623326213677153206539383410243797558749865055405315903078175197684269318157063715241746653449246845436032
def adaptiveNumericSpans1840_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1840_5Chunk0].flatten
def adaptiveSpanEven1840_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 920 0 adaptiveNumericSpans1840_5)
def adaptiveSpanWhole1840_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1840_5)
theorem adaptiveSpanNumericCheck1840_5 : coreNumericSpansCheck 1796 6 288 323 adaptiveNumericSpans1840_5 adaptiveRows1840 = true := by decide +kernel
theorem adaptiveSpanEvenCache1840_5 : adaptiveSpanEven1840_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1840_5 : adaptiveSpanEven1840_5.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1840_5 : adaptiveSpanEven1840_5.spans = coreEvenSpans 920 0 adaptiveNumericSpans1840_5 := by decide +kernel
theorem adaptiveSpanWholeCache1840_5 : adaptiveSpanWhole1840_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1840_5 : adaptiveSpanWhole1840_5.domainCheck 920 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1840_5 : adaptiveSpanWhole1840_5.spans = coreWholeSpans 0 adaptiveNumericSpans1840_5 := by decide +kernel
end Erdos883Verified
