import Erdos883AdaptiveSpan86416Level6TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_6 : adaptiveNumericSpans86416_6.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_6 : adaptiveSpanEven86416_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_6 : adaptiveSpanEven86416_6.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_6 : adaptiveSpanEven86416_6.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_6 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_6 : adaptiveSpanWhole86416_6.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_6 : adaptiveSpanWhole86416_6.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_6 : adaptiveSpanWhole86416_6.spans = coreWholeSpans 0 adaptiveNumericSpans86416_6 := by
  decide +kernel
end Erdos883Verified
