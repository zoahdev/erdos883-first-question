import Erdos883AdaptiveCertificate1666Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1666_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 12833332619459290359926672157473797799582259319641588362666150644786903128743109604183042503126242944807656403236549031748047258964592835557706564701430503822106840795641672680658364627807813308219902683429392547494855565014895470160432958294521217307189360959451824192
def adaptiveNumericSpans1666_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_0Chunk0].flatten
def adaptiveSpanEven1666_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_0)
def adaptiveSpanWhole1666_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_0)
theorem adaptiveSpanNumericCheck1666_0 : coreNumericSpansCheck 1626 6 480 1155 adaptiveNumericSpans1666_0 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_0 : adaptiveSpanEven1666_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_0 : adaptiveSpanEven1666_0.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_0 : adaptiveSpanEven1666_0.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_0 := by decide +kernel
theorem adaptiveSpanWholeCache1666_0 : adaptiveSpanWhole1666_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_0 : adaptiveSpanWhole1666_0.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_0 : adaptiveSpanWhole1666_0.spans = coreWholeSpans 0 adaptiveNumericSpans1666_0 := by decide +kernel
def adaptiveNumericSpans1666_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 7 7986202495676890934967128607395389819227839869655133516373511490891427927600728652245141447372389167831421599086657574193536764764245023261626013677115322038685989304797866854732373432404329370019000047632512
def adaptiveNumericSpans1666_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_1Chunk0].flatten
def adaptiveSpanEven1666_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_1)
def adaptiveSpanWhole1666_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_1)
theorem adaptiveSpanNumericCheck1666_1 : coreNumericSpansCheck 1626 6 240 385 adaptiveNumericSpans1666_1 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_1 : adaptiveSpanEven1666_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_1 : adaptiveSpanEven1666_1.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_1 : adaptiveSpanEven1666_1.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_1 := by decide +kernel
theorem adaptiveSpanWholeCache1666_1 : adaptiveSpanWhole1666_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_1 : adaptiveSpanWhole1666_1.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_1 : adaptiveSpanWhole1666_1.spans = coreWholeSpans 0 adaptiveNumericSpans1666_1 := by decide +kernel
def adaptiveNumericSpans1666_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 10123714387188994415665455845456330568542007076564237152901806125066518220388561125193271449552890272412441868480592458840733528292952467218540959163737572034664177936167528603826003879036571074122790583921349069289963629605188589586481280
def adaptiveNumericSpans1666_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_2Chunk0].flatten
def adaptiveSpanEven1666_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_2)
def adaptiveSpanWhole1666_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_2)
theorem adaptiveSpanNumericCheck1666_2 : coreNumericSpansCheck 1626 6 720 1001 adaptiveNumericSpans1666_2 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_2 : adaptiveSpanEven1666_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_2 : adaptiveSpanEven1666_2.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_2 : adaptiveSpanEven1666_2.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_2 := by decide +kernel
theorem adaptiveSpanWholeCache1666_2 : adaptiveSpanWhole1666_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_2 : adaptiveSpanWhole1666_2.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_2 : adaptiveSpanWhole1666_2.spans = coreWholeSpans 0 adaptiveNumericSpans1666_2 := by decide +kernel
def adaptiveNumericSpans1666_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 12833332619459290359926672157473797799582259319641588362666150644786903128743109604183042503727750768012269105456329823401871107783282478514861122931492083498341339452671388092558906834552581192246556864018550660586140582645528854966731010157147879742699909516867141760
def adaptiveNumericSpans1666_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_3Chunk0].flatten
def adaptiveSpanEven1666_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_3)
def adaptiveSpanWhole1666_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_3)
theorem adaptiveSpanNumericCheck1666_3 : coreNumericSpansCheck 1626 6 120 143 adaptiveNumericSpans1666_3 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_3 : adaptiveSpanEven1666_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_3 : adaptiveSpanEven1666_3.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_3 : adaptiveSpanEven1666_3.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_3 := by decide +kernel
theorem adaptiveSpanWholeCache1666_3 : adaptiveSpanWhole1666_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_3 : adaptiveSpanWhole1666_3.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_3 : adaptiveSpanWhole1666_3.spans = coreWholeSpans 0 adaptiveNumericSpans1666_3 := by decide +kernel
def adaptiveNumericSpans1666_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 17 85572847128502374712389161190541695596321538587927297740240053329930539046188229627276895618570800208647614967064874266952147900208280472139498340431976596211473673877709972362676873457036100260568058786695777467168476727758777451172143240932176939525700723231061262424664411506309530241929542674768288044277858822499781022363148975447743150935789510497424536714434639148383963820778806750340677745001790860426790111097416380566051876489800167307596783870689248755454420241195483563275968745722681648020979776
def adaptiveNumericSpans1666_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_4Chunk0].flatten
def adaptiveSpanEven1666_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_4)
def adaptiveSpanWhole1666_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_4)
theorem adaptiveSpanNumericCheck1666_4 : coreNumericSpansCheck 1626 6 192 221 adaptiveNumericSpans1666_4 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_4 : adaptiveSpanEven1666_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_4 : adaptiveSpanEven1666_4.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_4 : adaptiveSpanEven1666_4.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_4 := by decide +kernel
theorem adaptiveSpanWholeCache1666_4 : adaptiveSpanWhole1666_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_4 : adaptiveSpanWhole1666_4.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_4 : adaptiveSpanWhole1666_4.spans = coreWholeSpans 0 adaptiveNumericSpans1666_4 := by decide +kernel
def adaptiveNumericSpans1666_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 16 67505073648129644048356590766314559946801426051473718637210631225814584204010001131072908584050620843093378289479290885933823463811710504767091942459197508584074999391395701077672729410760066989388272890825109432182473343634482841367367315633580018507192609319658986624874165412855308081610488477683080072410894212370780170613020372016245380918281816701495300175326782733503945629052334527296603358357808863363229917928671284680230566079645385326878716265154339947746078584995904
def adaptiveNumericSpans1666_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1666_5Chunk0].flatten
def adaptiveSpanEven1666_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 833 0 adaptiveNumericSpans1666_5)
def adaptiveSpanWhole1666_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1666_5)
theorem adaptiveSpanNumericCheck1666_5 : coreNumericSpansCheck 1626 6 288 323 adaptiveNumericSpans1666_5 adaptiveRows1666 = true := by decide +kernel
theorem adaptiveSpanEvenCache1666_5 : adaptiveSpanEven1666_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1666_5 : adaptiveSpanEven1666_5.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1666_5 : adaptiveSpanEven1666_5.spans = coreEvenSpans 833 0 adaptiveNumericSpans1666_5 := by decide +kernel
theorem adaptiveSpanWholeCache1666_5 : adaptiveSpanWhole1666_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1666_5 : adaptiveSpanWhole1666_5.domainCheck 833 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1666_5 : adaptiveSpanWhole1666_5.spans = coreWholeSpans 0 adaptiveNumericSpans1666_5 := by decide +kernel
end Erdos883Verified
