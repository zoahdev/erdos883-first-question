import Erdos883AdaptiveSpan86416Level7TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_7 : adaptiveNumericSpans86416_7.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_7 : adaptiveSpanEven86416_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_7 : adaptiveSpanEven86416_7.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_7 : adaptiveSpanEven86416_7.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_7 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_7 : adaptiveSpanWhole86416_7.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_7 : adaptiveSpanWhole86416_7.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_7 : adaptiveSpanWhole86416_7.spans = coreWholeSpans 0 adaptiveNumericSpans86416_7 := by
  decide +kernel
end Erdos883Verified
