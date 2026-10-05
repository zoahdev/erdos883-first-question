import Erdos883AdaptiveSpan86416Level3TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_3 : adaptiveNumericSpans86416_3.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_3 : adaptiveSpanEven86416_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_3 : adaptiveSpanEven86416_3.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_3 : adaptiveSpanEven86416_3.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_3 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_3 : adaptiveSpanWhole86416_3.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_3 : adaptiveSpanWhole86416_3.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_3 : adaptiveSpanWhole86416_3.spans = coreWholeSpans 0 adaptiveNumericSpans86416_3 := by
  decide +kernel
end Erdos883Verified
