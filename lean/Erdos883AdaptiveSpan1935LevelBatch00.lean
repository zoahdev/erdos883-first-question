import Erdos883AdaptiveCertificate1935Data
import Erdos883AdaptiveSpanCompactCore
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
def adaptiveNumericSpans1935_0Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 9 14945350947678717894264962431517413072473353458536337936196642485348320588744844625388969896831526624785074083495178616358712490355188679784591507768002756724167878967674772958700636681977169792927099302345765872890381482759737117840936595386912274843345488790647996544
def adaptiveNumericSpans1935_0 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_0Chunk0].flatten
def adaptiveSpanEven1935_0 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_0)
def adaptiveSpanWhole1935_0 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_0)
theorem adaptiveSpanNumericCheck1935_0 : coreNumericSpansCheck 1888 6 480 1155 adaptiveNumericSpans1935_0 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_0 : adaptiveSpanEven1935_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_0 : adaptiveSpanEven1935_0.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_0 : adaptiveSpanEven1935_0.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_0 := by decide +kernel
theorem adaptiveSpanWholeCache1935_0 : adaptiveSpanWhole1935_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_0 : adaptiveSpanWhole1935_0.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_0 : adaptiveSpanWhole1935_0.spans = coreWholeSpans 0 adaptiveNumericSpans1935_0 := by decide +kernel
def adaptiveNumericSpans1935_1Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11789803077431540042767914478750613540139494631285420158316291067152302745075335930748919173488688574769233017426628911780188746890866703360889752092669655065663448981806719541735904193469319396554630364441217841586796307765687507501449344
def adaptiveNumericSpans1935_1 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_1Chunk0].flatten
def adaptiveSpanEven1935_1 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_1)
def adaptiveSpanWhole1935_1 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_1)
theorem adaptiveSpanNumericCheck1935_1 : coreNumericSpansCheck 1888 6 240 385 adaptiveNumericSpans1935_1 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_1 : adaptiveSpanEven1935_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_1 : adaptiveSpanEven1935_1.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_1 : adaptiveSpanEven1935_1.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_1 := by decide +kernel
theorem adaptiveSpanWholeCache1935_1 : adaptiveSpanWhole1935_1.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_1 : adaptiveSpanWhole1935_1.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_1 : adaptiveSpanWhole1935_1.spans = coreWholeSpans 0 adaptiveNumericSpans1935_1 := by decide +kernel
def adaptiveNumericSpans1935_2Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 8 11789803077431540042767914478750613540139494631285420158316291067152302745075335930748919173488688574769233017426628911780188746890866703360889752092669791052550748352814580973506581758439743930403133966340791346457744168400842982160334976
def adaptiveNumericSpans1935_2 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_2Chunk0].flatten
def adaptiveSpanEven1935_2 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_2)
def adaptiveSpanWhole1935_2 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_2)
theorem adaptiveSpanNumericCheck1935_2 : coreNumericSpansCheck 1888 6 720 1001 adaptiveNumericSpans1935_2 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_2 : adaptiveSpanEven1935_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_2 : adaptiveSpanEven1935_2.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_2 : adaptiveSpanEven1935_2.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_2 := by decide +kernel
theorem adaptiveSpanWholeCache1935_2 : adaptiveSpanWhole1935_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_2 : adaptiveSpanWhole1935_2.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_2 : adaptiveSpanWhole1935_2.spans = coreWholeSpans 0 adaptiveNumericSpans1935_2 := by decide +kernel
def adaptiveNumericSpans1935_3Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 13 38592630662609433038437628554875895820426725006401628917221749044375366768614566923825610723104187282042840912875400716404994103526698192326122431805046532377061392891299478714237663583580195956060959658770743632832832077265689696726942819594466947025507132616269632490188278076747378341739701970132122225886862903815421422295204379044362277561961861391884487793117122819645408474403176576
def adaptiveNumericSpans1935_3 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_3Chunk0].flatten
def adaptiveSpanEven1935_3 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_3)
def adaptiveSpanWhole1935_3 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_3)
theorem adaptiveSpanNumericCheck1935_3 : coreNumericSpansCheck 1888 6 120 143 adaptiveNumericSpans1935_3 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_3 : adaptiveSpanEven1935_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_3 : adaptiveSpanEven1935_3.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_3 : adaptiveSpanEven1935_3.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_3 := by decide +kernel
theorem adaptiveSpanWholeCache1935_3 : adaptiveSpanWhole1935_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_3 : adaptiveSpanWhole1935_3.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_3 : adaptiveSpanWhole1935_3.spans = coreWholeSpans 0 adaptiveNumericSpans1935_3 := by decide +kernel
def adaptiveNumericSpans1935_4Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 30444217559366253986570152706909621545049621886524920284992141951532329866014256540463640703776457139915671529105675329705025572039671148842641889049577705634780728724215620031823834555603400344686342926440080569531082603838171316180275339499587343534253406133633623566798228205576056648859615236153232927913345180347706737807014295809074921356792562259591296
def adaptiveNumericSpans1935_4 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_4Chunk0].flatten
def adaptiveSpanEven1935_4 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_4)
def adaptiveSpanWhole1935_4 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_4)
theorem adaptiveSpanNumericCheck1935_4 : coreNumericSpansCheck 1888 6 192 221 adaptiveNumericSpans1935_4 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_4 : adaptiveSpanEven1935_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_4 : adaptiveSpanEven1935_4.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_4 : adaptiveSpanEven1935_4.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_4 := by decide +kernel
theorem adaptiveSpanWholeCache1935_4 : adaptiveSpanWhole1935_4.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_4 : adaptiveSpanWhole1935_4.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_4 : adaptiveSpanWhole1935_4.spans = coreWholeSpans 0 adaptiveNumericSpans1935_4 := by decide +kernel
def adaptiveNumericSpans1935_5Chunk0 : List AdaptiveNumericSpan := adaptivePackedNumericSpans 12 30444217559366253986570152706909621545049621886524920284992141951532329866014256540463640704074719266392665536527900630794227030281524626846194932343623433269053727817061809151515684436393365165793709631497332872630637062790824396689788131648750023338664418867447288526585397013983109455273273901833795716682431855519498265972935364405228357064535405831913600
def adaptiveNumericSpans1935_5 : List AdaptiveNumericSpan := [adaptiveNumericSpans1935_5Chunk0].flatten
def adaptiveSpanEven1935_5 := adaptiveSpanTreeOfSpans (coreEvenSpans 968 0 adaptiveNumericSpans1935_5)
def adaptiveSpanWhole1935_5 := adaptiveSpanTreeOfSpans (coreWholeSpans 0 adaptiveNumericSpans1935_5)
theorem adaptiveSpanNumericCheck1935_5 : coreNumericSpansCheck 1888 6 288 323 adaptiveNumericSpans1935_5 adaptiveRows1935 = true := by decide +kernel
theorem adaptiveSpanEvenCache1935_5 : adaptiveSpanEven1935_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain1935_5 : adaptiveSpanEven1935_5.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanEvenEntries1935_5 : adaptiveSpanEven1935_5.spans = coreEvenSpans 968 0 adaptiveNumericSpans1935_5 := by decide +kernel
theorem adaptiveSpanWholeCache1935_5 : adaptiveSpanWhole1935_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain1935_5 : adaptiveSpanWhole1935_5.domainCheck 968 = true := by decide +kernel
theorem adaptiveSpanWholeEntries1935_5 : adaptiveSpanWhole1935_5.spans = coreWholeSpans 0 adaptiveNumericSpans1935_5 := by decide +kernel
end Erdos883Verified
