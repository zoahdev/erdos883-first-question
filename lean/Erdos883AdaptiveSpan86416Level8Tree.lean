import Erdos883AdaptiveSpan86416Level8TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_8 : adaptiveNumericSpans86416_8.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_8 : adaptiveSpanEven86416_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_8 : adaptiveSpanEven86416_8.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_8 : adaptiveSpanEven86416_8.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_8 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_8 : adaptiveSpanWhole86416_8.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_8 : adaptiveSpanWhole86416_8.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_8 : adaptiveSpanWhole86416_8.spans = coreWholeSpans 0 adaptiveNumericSpans86416_8 := by
  decide +kernel
end Erdos883Verified
