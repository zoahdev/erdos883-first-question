import Erdos883AdaptiveSpan86416Level2TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_2 : adaptiveNumericSpans86416_2.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_2 : adaptiveSpanEven86416_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_2 : adaptiveSpanEven86416_2.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_2 : adaptiveSpanEven86416_2.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_2 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_2 : adaptiveSpanWhole86416_2.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_2 : adaptiveSpanWhole86416_2.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_2 : adaptiveSpanWhole86416_2.spans = coreWholeSpans 0 adaptiveNumericSpans86416_2 := by
  decide +kernel
end Erdos883Verified
